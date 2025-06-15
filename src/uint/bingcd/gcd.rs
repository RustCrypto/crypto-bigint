use crate::uint::bingcd::tools::{const_max, const_min};
use crate::{NonZero, Odd, U64, U128, Uint};

impl<const LIMBS: usize> NonZero<Uint<LIMBS>> {
    /// Compute the greatest common divisor of `self` and `rhs`.
    pub const fn bingcd(&self, rhs: &Uint<LIMBS>) -> Self {
        let val = self.as_ref();
        // Leverage two GCD identity rules to make self and rhs odd.
        // 1) gcd(2a, 2b) = 2 * gcd(a, b)
        // 2) gcd(a, 2b) = gcd(a, b) if a is odd.
        let i = val.is_nonzero().select_u32(0, val.trailing_zeros());
        let j = rhs.is_nonzero().select_u32(0, rhs.trailing_zeros());
        let k = const_min(i, j);

        val.shr(i)
            .to_odd()
            .expect("val.shr(i) is odd by construction")
            .bingcd(rhs)
            .as_ref()
            .shl(k)
            .to_nz()
            .expect("gcd of non-zero element with another element is non-zero")
    }
}

impl<const LIMBS: usize> Odd<Uint<LIMBS>> {
    const BITS: u32 = Uint::<LIMBS>::BITS;

    /// Compute the greatest common divisor of `self` and `rhs` using the Binary GCD algorithm.
    ///
    /// This function switches between the "classic" and "optimized" algorithm at a best-effort
    /// threshold. When using [Uint]s with `LIMBS` close to the threshold, it may be useful to
    /// manually test whether the classic or optimized algorithm is faster for your machine.
    #[inline(always)]
    pub const fn bingcd(&self, rhs: &Uint<LIMBS>) -> Self {
        // Todo: tweak this threshold
        // Note: we're swapping the parameters here for greater readability: Pornin's Algorithm 1
        // and Algorithm 2 both require the second argument (m) to be odd. Given that the gcd
        // is the same, regardless of the order of the parameters, this swap does not affect the
        // result.
        if LIMBS < 8 {
            self.classic_bingcd(rhs)
        } else {
            self.optimized_bingcd(rhs)
        }
    }

    /// Computes `gcd(self, rhs)`, leveraging the (a constant time implementation of) the classic
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
        while j < (2 * Self::BITS - 1) {
            j += 1;

            let a_odd = a.is_odd();

            // swap if a odd and a < b
            let a_lt_b = Uint::lt(&a, &b);
            let do_swap = a_odd.and(a_lt_b);
            Uint::conditional_swap(&mut a, &mut b, do_swap);

            // subtract b from a when a is odd
            a = a.wrapping_sub(&Uint::select(&Uint::ZERO, &b, a_odd));

            // Div a by two.
            // safe to vartime; shr_vartime is variable in the value of shift only. Since this shift
            // is a public constant, the constant time property of this algorithm is not impacted.
            a = a.shr_vartime(1);
        }

        b.to_odd()
            .expect("gcd of an odd value with something else is always odd")
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
    #[inline(always)]
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
    #[inline(always)]
    pub const fn optimized_bingcd_<const K: u32, const LIMBS_K: usize, const LIMBS_2K: usize>(
        &self,
        rhs: &Uint<LIMBS>,
    ) -> Self {
        // (self, rhs) corresponds to (m, y) in the Algorithm 1 notation.
        let (mut a, mut b) = (*rhs, *self.as_ref());

        let iterations = (2 * Self::BITS - 1).div_ceil(K);
        let mut i = 0;
        while i < iterations {
            i += 1;

            // Construct a_ and b_ as the summary of a and b, respectively.
            let n = const_max(2 * K, const_max(a.bits(), b.bits()));
            let a_ = a.compact::<K, LIMBS_2K>(n);
            let b_ = b.compact::<K, LIMBS_2K>(n);

            // Compute the K-1 iteration update matrix from a_ and b_
            // Safe to vartime; function executes in time variable in `iterations` only, which is
            // a public constant K-1 here.
            let (matrix, log_upper_bound) = b_
                .to_odd()
                .expect("b_ is always odd")
                .partial_binxgcd_vartime::<LIMBS_K>(&a_, K - 1);

            // Update `a` and `b` using the update matrix
            let (updated_a, updated_b) = matrix.extended_apply_to((a, b));

            a = updated_a
                .div_2k(log_upper_bound)
                .abs_drop_extension()
                .expect("extension is zero");
            b = updated_b
                .div_2k(log_upper_bound)
                .abs_drop_extension()
                .expect("extension is zero");
        }

        b.to_odd()
            .expect("gcd of an odd value with something else is always odd")
    }
}

#[cfg(feature = "rand_core")]
#[cfg(test)]
mod tests {

    mod test_bingcd_small {
        use crate::{Gcd, Random, U64, U128, U192, U256, U384, U512, U1024, U2048, U4096, Uint};
        use rand_chacha::ChaCha8Rng;
        use rand_core::{RngCore, SeedableRng};

        fn classic_bingcd_test<const LIMBS: usize>(lhs: Uint<LIMBS>, rhs: Uint<LIMBS>)
        where
            Uint<LIMBS>: Gcd<Output = Uint<LIMBS>>,
        {
            let gcd = lhs.gcd(&rhs);
            let bingcd = lhs.to_odd().unwrap().classic_bingcd(&rhs);
            assert_eq!(gcd, bingcd);
        }

        fn classic_bingcd_tests<const LIMBS: usize>(rng: &mut impl RngCore)
        where
            Uint<LIMBS>: Gcd<Output = Uint<LIMBS>>,
        {
            // Edge cases
            classic_bingcd_test(Uint::ONE, Uint::ZERO);
            classic_bingcd_test(Uint::ONE, Uint::ONE);
            classic_bingcd_test(Uint::ONE, Uint::MAX);
            classic_bingcd_test(Uint::MAX, Uint::ZERO);
            classic_bingcd_test(Uint::MAX, Uint::ONE);
            classic_bingcd_test(Uint::MAX, Uint::MAX);

            // Randomized test cases
            for _ in 0..1000 {
                let x = Uint::<LIMBS>::random(rng).bitor(&Uint::ONE);
                let y = Uint::<LIMBS>::random(rng);
                classic_bingcd_test(x, y);
            }
        }

        #[test]
        fn test_classic_bingcd() {
            let mut rng = ChaCha8Rng::from_seed(*b"01234567890123456789012345678901");
            classic_bingcd_tests::<{ U64::LIMBS }>(&mut rng);
            classic_bingcd_tests::<{ U128::LIMBS }>(&mut rng);
            classic_bingcd_tests::<{ U192::LIMBS }>(&mut rng);
            classic_bingcd_tests::<{ U256::LIMBS }>(&mut rng);
            classic_bingcd_tests::<{ U384::LIMBS }>(&mut rng);
            classic_bingcd_tests::<{ U512::LIMBS }>(&mut rng);
            classic_bingcd_tests::<{ U1024::LIMBS }>(&mut rng);
            classic_bingcd_tests::<{ U2048::LIMBS }>(&mut rng);
            classic_bingcd_tests::<{ U4096::LIMBS }>(&mut rng);
        }
    }

    mod test_bingcd_large {
        use crate::{Gcd, Random, U128, U192, U256, U384, U512, U1024, U2048, U4096, Uint};
        use rand_chacha::ChaCha8Rng;
        use rand_core::{RngCore, SeedableRng};

        fn optimized_bingcd_test<const LIMBS: usize>(lhs: Uint<LIMBS>, rhs: Uint<LIMBS>)
        where
            Uint<LIMBS>: Gcd<Output = Uint<LIMBS>>,
        {
            let gcd = lhs.gcd(&rhs);
            let bingcd = lhs.to_odd().unwrap().optimized_bingcd(&rhs);
            assert_eq!(gcd, bingcd);
        }

        fn optimized_bingcd_tests<const LIMBS: usize>(rng: &mut impl RngCore)
        where
            Uint<LIMBS>: Gcd<Output = Uint<LIMBS>>,
        {
            // Edge cases
            optimized_bingcd_test(Uint::ONE, Uint::ZERO);
            optimized_bingcd_test(Uint::ONE, Uint::ONE);
            optimized_bingcd_test(Uint::ONE, Uint::MAX);
            optimized_bingcd_test(Uint::MAX, Uint::ZERO);
            optimized_bingcd_test(Uint::MAX, Uint::ONE);
            optimized_bingcd_test(Uint::MAX, Uint::MAX);

            // Randomized testing
            for _ in 0..1000 {
                let x = Uint::<LIMBS>::random(rng).bitor(&Uint::ONE);
                let y = Uint::<LIMBS>::random(rng);
                optimized_bingcd_test(x, y);
            }
        }

        #[test]
        fn test_optimized_bingcd() {
            let mut rng = ChaCha8Rng::from_seed(*b"01234567890123456789012345678901");

            // Not applicable for U64
            optimized_bingcd_tests::<{ U128::LIMBS }>(&mut rng);
            optimized_bingcd_tests::<{ U192::LIMBS }>(&mut rng);
            optimized_bingcd_tests::<{ U256::LIMBS }>(&mut rng);
            optimized_bingcd_tests::<{ U384::LIMBS }>(&mut rng);
            optimized_bingcd_tests::<{ U512::LIMBS }>(&mut rng);
            optimized_bingcd_tests::<{ U1024::LIMBS }>(&mut rng);
            optimized_bingcd_tests::<{ U2048::LIMBS }>(&mut rng);
            optimized_bingcd_tests::<{ U4096::LIMBS }>(&mut rng);
        }
    }
}
