use crate::const_choice::u32_max;
use crate::{ConstChoice, Limb, Odd, U64, U128, Uint};

impl<const LIMBS: usize> Odd<Uint<LIMBS>> {
    /// The minimal number of binary GCD iterations required to guarantee successful completion.
    const MINIMAL_BINGCD_ITERATIONS: u32 = 2 * Self::BITS - 1;

    /// Computes `gcd(self, rhs)`, leveraging (a constant time implementation of) the classic
    /// Binary GCD algorithm.
    ///
    /// Note: this algorithm is efficient for [Uint]s with relatively few `LIMBS`.
    ///
    /// Ref: Pornin, Optimized Binary GCD for Modular Inversion, Algorithm 1.
    /// <https://eprint.iacr.org/2020/972.pdf>
    #[inline]
    pub const fn classic_bingcd(&self, rhs: &Uint<LIMBS>) -> Self {
        // (self, rhs) corresponds to (m, y) in the Algorithm 1 notation.
        let (mut a, mut b) = (*rhs, *self.as_ref());
        let mut j = 0;
        while j < Self::MINIMAL_BINGCD_ITERATIONS {
            Self::bingcd_step(&mut a, &mut b);
            j += 1;
        }

        b.to_odd()
            .expect("gcd of an odd value with something else is always odd")
    }

    /// Variable time equivalent of [`Self::classic_bingcd`].
    #[inline]
    pub const fn classic_bingcd_vartime(&self, rhs: &Uint<LIMBS>) -> Self {
        // (self, rhs) corresponds to (m, y) in the Algorithm 1 notation.
        let (mut a, mut b) = (*rhs, *self.as_ref());
        while a.is_nonzero().to_bool_vartime() {
            Self::bingcd_step(&mut a, &mut b);
        }

        b.to_odd()
            .expect("gcd of an odd value with something else is always odd")
    }

    /// Binary GCD update step.
    ///
    /// This is a condensed, constant time execution of the following algorithm:
    /// ```text
    /// if a mod 2 == 1
    ///    if a < b
    ///        (a, b) ← (b, a)
    ///    a ← a - b
    /// a ← a/2
    /// ```
    ///
    /// Note: assumes `b` to be odd. Might yield an incorrect result if this is not the case.
    ///
    /// Ref: Pornin, Algorithm 1, L3-9, <https://eprint.iacr.org/2020/972.pdf>.
    #[inline(always)]
    pub(super) const fn bingcd_step(
        a: &mut Uint<LIMBS>,
        b: &mut Uint<LIMBS>,
    ) -> (ConstChoice, ConstChoice) {
        let a_odd = a.is_odd();
        let (a_sub_b, borrow) = a.borrowing_sub(&Uint::select(&Uint::ZERO, b, a_odd), Limb::ZERO);
        let swap = borrow.is_nonzero();
        *b = Uint::select(b, a, swap);
        *a = Uint::select(&a_sub_b, &a_sub_b.wrapping_neg(), swap).shr1();
        (a_odd, swap)
    }

    /// Computes `gcd(self, rhs)`, leveraging the optimized Binary GCD algorithm.
    ///
    /// Note: this algorithm becomes more efficient than the classical algorithm for [Uint]s with
    /// relatively many `LIMBS`. A best-effort threshold is presented in [Self::bingcd].
    ///
    /// Note: the full algorithm has an additional parameter; this function selects the best-effort
    /// value for this parameter. You might be able to further tune your performance by calling the
    /// [Self::optimized_bingcd_] function directly.
    ///
    /// Ref: Pornin, Optimized Binary GCD for Modular Inversion, Algorithm 2.
    /// <https://eprint.iacr.org/2020/972.pdf>
    #[inline]
    pub const fn optimized_bingcd(&self, rhs: &Uint<LIMBS>) -> Self {
        self.optimized_bingcd_::<{ U64::BITS }, { U64::LIMBS }, { U128::LIMBS }>(rhs)
    }

    /// Computes `gcd(self, rhs)`, leveraging the optimized Binary GCD algorithm.
    ///
    /// Ref: Pornin, Optimized Binary GCD for Modular Inversion, Algorithm 2.
    /// <https://eprint.iacr.org/2020/972.pdf>
    ///
    /// In summary, the optimized algorithm does not operate on `self` and `rhs` directly, but
    /// instead of condensed summaries that fit in few registers. Based on these summaries, an
    /// update matrix is constructed by which `self` and `rhs` are updated in larger steps.
    ///
    /// This function is generic over the following three values:
    /// - `K`: the number of bits used when summarizing `self` and `rhs` for the inner loop. The
    ///   `K+1` top bits and `K-1` least significant bits are selected. It is recommended to keep
    ///   `K` close to a (multiple of) the number of bits that fit in a single register.
    /// - `LIMBS_K`: should be chosen as the minimum number s.t. [`Uint::<LIMBS>::BITS`] `≥ K`,
    /// - `LIMBS_2K`: should be chosen as the minimum number s.t. [`Uint::<LIMBS>::BITS`] `≥ 2K`.
    #[inline]
    pub const fn optimized_bingcd_<const K: u32, const LIMBS_K: usize, const LIMBS_2K: usize>(
        &self,
        rhs: &Uint<LIMBS>,
    ) -> Self {
        let (mut a, mut b) = (*self.as_ref(), *rhs);

        let iterations = Self::MINIMAL_BINGCD_ITERATIONS.div_ceil(K);
        let mut i = 0;
        while i < iterations {
            i += 1;

            // Construct a_ and b_ as the summary of a and b, respectively.
            let n = u32_max(2 * K, a.bitor(&b).bits());
            let a_ = a.compact::<K, LIMBS_2K>(n);
            let b_ = b.compact::<K, LIMBS_2K>(n);

            // Compute the K-1 iteration update matrix from a_ and b_
            // Safe to vartime; function executes in time variable in `iterations` only, which is
            // a public constant K-1 here.
            let (.., matrix) = a_
                .to_odd()
                .expect("a_ is always odd")
                .partial_binxgcd::<LIMBS_K, false>(&b_, K - 1);

            // Update `a` and `b` using the update matrix
            // Safe to use vartime: the number of doublings is constant (K-1).
            let (updated_a, updated_b) = matrix.extended_apply_to_vartime::<LIMBS>((a, b));
            (a, _) = updated_a.wrapping_drop_extension();
            (b, _) = updated_b.wrapping_drop_extension();
        }

        a.to_odd()
            .expect("gcd of an odd value with something else is always odd")
    }

    /// Variable time equivalent of [`Self::optimized_bingcd`].
    #[inline]
    pub const fn optimized_bingcd_vartime(&self, rhs: &Uint<LIMBS>) -> Self {
        self.optimized_bingcd_vartime_::<{ U64::BITS }, { U64::LIMBS }, { U128::LIMBS }>(rhs)
    }

    /// Variable time equivalent of [`Self::optimized_bingcd_`].
    #[inline]
    pub const fn optimized_bingcd_vartime_<
        const K: u32,
        const LIMBS_K: usize,
        const LIMBS_2K: usize,
    >(
        &self,
        rhs: &Uint<LIMBS>,
    ) -> Self {
        let (mut a, mut b) = (*self.as_ref(), *rhs);

        while b.is_nonzero().to_bool_vartime() {
            // Construct a_ and b_ as the summary of a and b, respectively.
            let n = u32_max(2 * K, u32_max(a.bits_vartime(), b.bits_vartime()));
            let a_ = a.compact_vartime::<K, LIMBS_2K>(n);
            let b_ = b.compact_vartime::<K, LIMBS_2K>(n);

            // Compute the K-1 iteration update matrix from a_ and b_
            // Safe to vartime; function executes in time variable in `iterations` only, which is
            // a public constant K-1 here.
            let (.., matrix) = a_
                .to_odd()
                .expect("a_ is always odd")
                .partial_binxgcd::<LIMBS_K, false>(&b_, K - 1);

            // Update `a` and `b` using the update matrix
            let (updated_a, updated_b) = matrix.extended_apply_to_vartime((a, b));
            (a, _) = updated_a.wrapping_drop_extension();
            (b, _) = updated_b.wrapping_drop_extension();
        }

        a.to_odd()
            .expect("gcd of an odd value with something else is always odd")
    }
}

#[cfg(all(test, not(miri)))]
mod tests {

    mod test_classic_bingcd {
        use crate::{Int, U64, U128, U192, U256, U384, U512, U1024, U2048, U4096, Uint};

        fn classic_bingcd_test<const LIMBS: usize>(
            lhs: Uint<LIMBS>,
            rhs: Uint<LIMBS>,
            target: Uint<LIMBS>,
        ) {
            assert_eq!(
                lhs.to_odd().unwrap().classic_bingcd(&rhs),
                target.to_odd().unwrap()
            );
            assert_eq!(
                lhs.to_odd().unwrap().classic_bingcd_vartime(&rhs),
                target.to_odd().unwrap()
            );
        }

        fn classic_bingcd_tests<const LIMBS: usize>() {
            classic_bingcd_test(Uint::<LIMBS>::ONE, Uint::ZERO, Uint::ONE);
            classic_bingcd_test(Uint::<LIMBS>::ONE, Uint::ONE, Uint::ONE);
            classic_bingcd_test(Uint::<LIMBS>::ONE, Int::MAX.abs(), Uint::ONE);
            classic_bingcd_test(Uint::<LIMBS>::ONE, Int::MIN.abs(), Uint::ONE);
            classic_bingcd_test(Uint::<LIMBS>::ONE, Uint::MAX, Uint::ONE);
            classic_bingcd_test(Int::<LIMBS>::MAX.abs(), Uint::ZERO, Int::MAX.abs());
            classic_bingcd_test(Int::<LIMBS>::MAX.abs(), Uint::ONE, Uint::ONE);
            classic_bingcd_test(Int::<LIMBS>::MAX.abs(), Int::MAX.abs(), Int::MAX.abs());
            classic_bingcd_test(Int::<LIMBS>::MAX.abs(), Int::MIN.abs(), Uint::ONE);
            classic_bingcd_test(Int::<LIMBS>::MAX.abs(), Uint::MAX, Uint::ONE);
            classic_bingcd_test(Uint::<LIMBS>::MAX, Uint::ZERO, Uint::MAX);
            classic_bingcd_test(Uint::<LIMBS>::MAX, Uint::ONE, Uint::ONE);
            classic_bingcd_test(Uint::<LIMBS>::MAX, Int::MAX.abs(), Uint::ONE);
            classic_bingcd_test(Uint::<LIMBS>::MAX, Int::MIN.abs(), Uint::ONE);
            classic_bingcd_test(Uint::<LIMBS>::MAX, Uint::MAX, Uint::MAX);
        }

        #[test]
        fn test_classic_bingcd() {
            classic_bingcd_tests::<{ U64::LIMBS }>();
            classic_bingcd_tests::<{ U128::LIMBS }>();
            classic_bingcd_tests::<{ U192::LIMBS }>();
            classic_bingcd_tests::<{ U256::LIMBS }>();
            classic_bingcd_tests::<{ U384::LIMBS }>();
            classic_bingcd_tests::<{ U512::LIMBS }>();
            classic_bingcd_tests::<{ U1024::LIMBS }>();
            classic_bingcd_tests::<{ U2048::LIMBS }>();
            classic_bingcd_tests::<{ U4096::LIMBS }>();
        }
    }

    mod test_optimized_bingcd {
        use crate::{Int, U128, U192, U256, U384, U512, U1024, U2048, U4096, Uint};

        fn optimized_bingcd_test<const LIMBS: usize>(
            lhs: Uint<LIMBS>,
            rhs: Uint<LIMBS>,
            target: Uint<LIMBS>,
        ) {
            assert_eq!(
                lhs.to_odd().unwrap().optimized_bingcd(&rhs),
                target.to_odd().unwrap()
            );
            assert_eq!(
                lhs.to_odd().unwrap().optimized_bingcd_vartime(&rhs),
                target.to_odd().unwrap()
            );
        }

        fn optimized_bingcd_tests<const LIMBS: usize>() {
            optimized_bingcd_test(Uint::<LIMBS>::ONE, Uint::ZERO, Uint::ONE);
            optimized_bingcd_test(Uint::<LIMBS>::ONE, Uint::ONE, Uint::ONE);
            optimized_bingcd_test(Uint::<LIMBS>::ONE, Int::MAX.abs(), Uint::ONE);
            optimized_bingcd_test(Uint::<LIMBS>::ONE, Int::MIN.abs(), Uint::ONE);
            optimized_bingcd_test(Uint::<LIMBS>::ONE, Uint::MAX, Uint::ONE);
            optimized_bingcd_test(Int::<LIMBS>::MAX.abs(), Uint::ZERO, Int::MAX.abs());
            optimized_bingcd_test(Int::<LIMBS>::MAX.abs(), Uint::ONE, Uint::ONE);
            optimized_bingcd_test(Int::<LIMBS>::MAX.abs(), Int::MAX.abs(), Int::MAX.abs());
            optimized_bingcd_test(Int::<LIMBS>::MAX.abs(), Int::MIN.abs(), Uint::ONE);
            optimized_bingcd_test(Int::<LIMBS>::MAX.abs(), Uint::MAX, Uint::ONE);
            optimized_bingcd_test(Uint::<LIMBS>::MAX, Uint::ZERO, Uint::MAX);
            optimized_bingcd_test(Uint::<LIMBS>::MAX, Uint::ONE, Uint::ONE);
            optimized_bingcd_test(Uint::<LIMBS>::MAX, Int::MAX.abs(), Uint::ONE);
            optimized_bingcd_test(Uint::<LIMBS>::MAX, Int::MIN.abs(), Uint::ONE);
            optimized_bingcd_test(Uint::<LIMBS>::MAX, Uint::MAX, Uint::MAX);
        }

        #[test]
        fn test_optimized_bingcd() {
            // Not applicable for U64
            optimized_bingcd_tests::<{ U128::LIMBS }>();
            optimized_bingcd_tests::<{ U192::LIMBS }>();
            optimized_bingcd_tests::<{ U256::LIMBS }>();
            optimized_bingcd_tests::<{ U384::LIMBS }>();
            optimized_bingcd_tests::<{ U512::LIMBS }>();
            optimized_bingcd_tests::<{ U1024::LIMBS }>();
            optimized_bingcd_tests::<{ U2048::LIMBS }>();
            optimized_bingcd_tests::<{ U4096::LIMBS }>();
        }
    }
}
