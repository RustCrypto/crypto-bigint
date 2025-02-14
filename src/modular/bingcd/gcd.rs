use crate::modular::bingcd::tools::const_max;
use crate::{ConstChoice, Odd, Uint, U128, U64};

impl<const LIMBS: usize> Odd<Uint<LIMBS>> {
    /// The minimal number of iterations required to ensure the Binary GCD algorithm terminates and
    /// returns the proper value.
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
    #[inline]
    const fn bingcd_step(a: &mut Uint<LIMBS>, b: &mut Uint<LIMBS>) {
        let a_odd = a.is_odd();
        let a_lt_b = Uint::lt(a, b);
        Uint::conditional_swap(a, b, a_odd.and(a_lt_b));
        *a = a
            .wrapping_sub(&Uint::select(&Uint::ZERO, b, a_odd))
            .shr_vartime(1);
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
    /// - `LIMBS_K`: should be chosen as the minimum number s.t. `Uint::<LIMBS>::BITS ≥ K`,
    /// - `LIMBS_2K`: should be chosen as the minimum number s.t. `Uint::<LIMBS>::BITS ≥ 2K`.
    #[inline]
    pub const fn optimized_bingcd_<const K: u32, const LIMBS_K: usize, const LIMBS_2K: usize>(
        &self,
        rhs: &Uint<LIMBS>,
    ) -> Self {
        let (mut a, mut b) = (*self.as_ref(), *rhs);

        let mut i = 0;
        while i < Self::MINIMAL_BINGCD_ITERATIONS.div_ceil(K - 1) {
            i += 1;

            // Construct a_ and b_ as the summary of a and b, respectively.
            let n = const_max(2 * K, const_max(a.bits(), b.bits()));
            let a_ = a.compact::<K, LIMBS_2K>(n);
            let b_ = b.compact::<K, LIMBS_2K>(n);

            // Compute the K-1 iteration update matrix from a_ and b_
            // Safe to vartime; function executes in time variable in `iterations` only, which is
            // a public constant K-1 here.
            let (.., matrix, _) = a_
                .to_odd()
                .expect("a_ is always odd")
                .partial_binxgcd_vartime::<LIMBS_K>(&b_, K - 1, ConstChoice::FALSE);

            // Update `a` and `b` using the update matrix
            let (updated_a, updated_b) = matrix.extended_apply_to((a, b));
            (a, _) = updated_a.div_2k_vartime(K - 1).wrapping_drop_extension();
            (b, _) = updated_b.div_2k_vartime(K - 1).wrapping_drop_extension();
        }

        a.to_odd()
            .expect("gcd of an odd value with something else is always odd")
    }
}

#[cfg(feature = "rand_core")]
#[cfg(test)]
mod tests {

    mod test_classic_bingcd {
        use crate::{
            Gcd, Int, Random, Uint, U1024, U128, U192, U2048, U256, U384, U4096, U512, U64,
        };
        use rand_core::OsRng;

        fn classic_bingcd_test<const LIMBS: usize>(lhs: Uint<LIMBS>, rhs: Uint<LIMBS>)
        where
            Uint<LIMBS>: Gcd<Output = Uint<LIMBS>>,
        {
            let gcd = lhs.gcd(&rhs);
            let bingcd = lhs.to_odd().unwrap().classic_bingcd(&rhs);
            assert_eq!(gcd, bingcd);
        }

        fn classic_bingcd_tests<const LIMBS: usize>()
        where
            Uint<LIMBS>: Gcd<Output = Uint<LIMBS>>,
        {
            // Edge cases
            classic_bingcd_test(Uint::ONE, Uint::ZERO);
            classic_bingcd_test(Uint::ONE, Uint::ONE);
            classic_bingcd_test(Uint::ONE, Int::MAX.abs());
            classic_bingcd_test(Uint::ONE, Int::MIN.abs());
            classic_bingcd_test(Uint::ONE, Uint::MAX);
            classic_bingcd_test(Int::MAX.abs(), Uint::ZERO);
            classic_bingcd_test(Int::MAX.abs(), Uint::ONE);
            classic_bingcd_test(Int::MAX.abs(), Int::MAX.abs());
            classic_bingcd_test(Int::MAX.abs(), Int::MIN.abs());
            classic_bingcd_test(Int::MAX.abs(), Uint::MAX);
            classic_bingcd_test(Uint::MAX, Uint::ZERO);
            classic_bingcd_test(Uint::MAX, Uint::ONE);
            classic_bingcd_test(Uint::MAX, Int::MAX.abs());
            classic_bingcd_test(Uint::MAX, Int::MIN.abs());
            classic_bingcd_test(Uint::MAX, Uint::MAX);

            // Randomized test cases
            for _ in 0..1000 {
                let x = Uint::<LIMBS>::random(&mut OsRng).bitor(&Uint::ONE);
                let y = Uint::<LIMBS>::random(&mut OsRng);
                classic_bingcd_test(x, y);
            }
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
        use crate::{Gcd, Int, Random, Uint, U1024, U128, U192, U2048, U256, U384, U4096, U512};
        use rand_core::OsRng;

        fn optimized_bingcd_test<const LIMBS: usize>(lhs: Uint<LIMBS>, rhs: Uint<LIMBS>)
        where
            Uint<LIMBS>: Gcd<Output = Uint<LIMBS>>,
        {
            let gcd = lhs.gcd(&rhs);
            let bingcd = lhs.to_odd().unwrap().optimized_bingcd(&rhs);
            assert_eq!(gcd, bingcd);
        }

        fn optimized_bingcd_tests<const LIMBS: usize>()
        where
            Uint<LIMBS>: Gcd<Output = Uint<LIMBS>>,
        {
            // Edge cases
            optimized_bingcd_test(Uint::ONE, Uint::ZERO);
            optimized_bingcd_test(Uint::ONE, Uint::ONE);
            optimized_bingcd_test(Uint::ONE, Int::MAX.abs());
            optimized_bingcd_test(Uint::ONE, Int::MIN.abs());
            optimized_bingcd_test(Uint::ONE, Uint::MAX);
            optimized_bingcd_test(Int::MAX.abs(), Uint::ZERO);
            optimized_bingcd_test(Int::MAX.abs(), Uint::ONE);
            optimized_bingcd_test(Int::MAX.abs(), Int::MAX.abs());
            optimized_bingcd_test(Int::MAX.abs(), Int::MIN.abs());
            optimized_bingcd_test(Int::MAX.abs(), Uint::MAX);
            optimized_bingcd_test(Uint::MAX, Uint::ZERO);
            optimized_bingcd_test(Uint::MAX, Uint::ONE);
            optimized_bingcd_test(Uint::MAX, Int::MAX.abs());
            optimized_bingcd_test(Uint::MAX, Int::MIN.abs());
            optimized_bingcd_test(Uint::MAX, Uint::MAX);

            // Randomized testing
            for _ in 0..1000 {
                let x = Uint::<LIMBS>::random(&mut OsRng).bitor(&Uint::ONE);
                let y = Uint::<LIMBS>::random(&mut OsRng);
                optimized_bingcd_test(x, y);
            }
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
