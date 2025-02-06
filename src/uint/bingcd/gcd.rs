use crate::uint::bingcd::tools::{const_max, const_min};
use crate::{NonZero, Odd, Uint, U128, U64};

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
            .expect("self is odd by construction")
            .bingcd(rhs)
            .as_ref()
            .shl(k)
            .to_nz()
            .expect("gcd of non-zero element with zero is non-zero")
    }
}

impl<const LIMBS: usize> Odd<Uint<LIMBS>> {
    /// Total size of the represented integer in bits.
    pub const BITS: u32 = Uint::<LIMBS>::BITS;

    /// Compute the greatest common divisor of `self` and `rhs`.
    #[inline(always)]
    pub const fn bingcd(&self, rhs: &Uint<LIMBS>) -> Self {
        // Todo: tweak this threshold
        if LIMBS < 8 {
            self.bingcd_small(rhs)
        } else {
            self.bingcd_large::<{ U64::BITS - 2 }, { U64::LIMBS }, { U128::LIMBS }>(rhs)
        }
    }

    /// Computes `gcd(self, rhs)`, leveraging the Binary GCD algorithm.
    /// Is efficient only for relatively small `LIMBS`.
    #[inline]
    pub const fn bingcd_small(&self, rhs: &Uint<LIMBS>) -> Self {
        let (mut a, mut b) = (*self.as_ref(), *rhs);
        let mut j = 0;
        while j < (2 * Self::BITS - 1) {
            Self::bingcd_step(&mut a, &mut b);
            j += 1;
        }

        a.to_odd()
            .expect("gcd of an odd value with something else is always odd")
    }

    /// Binary GCD update step.
    ///
    /// This is a condensed, constant time execution of the following algorithm:
    /// ```text
    /// if b mod 2 == 1
    ///    if a > b
    ///        (a, b) ← (b, a)
    ///    b ← b - a
    /// b ← b/2
    /// ```
    /// Ref: Pornin, Algorithm 2, L8-17, <https://eprint.iacr.org/2020/972.pdf>.
    #[inline]
    const fn bingcd_step(a: &mut Uint<LIMBS>, b: &mut Uint<LIMBS>) {
        let b_odd = b.is_odd();
        let a_gt_b = Uint::gt(a, b);
        Uint::conditional_swap(a, b, b_odd.and(a_gt_b));
        *b = Uint::select(b, &b.wrapping_sub(a), b_odd).shr_vartime(1);
    }

    /// Computes `gcd(self, rhs)`, leveraging the Binary GCD algorithm.
    /// Is efficient for larger `LIMBS`.
    #[inline(always)]
    pub const fn bingcd_large<const K: u32, const LIMBS_K: usize, const LIMBS_2K: usize>(
        &self,
        rhs: &Uint<LIMBS>,
    ) -> Self {
        let (mut a, mut b) = (*self.as_ref(), *rhs);

        let mut i = 0;
        while i < (2 * Self::BITS - 1).div_ceil(K) {
            i += 1;

            // Construct a_ and b_ as the summary of a and b, respectively.
            let n = const_max(2 * K, const_max(a.bits(), b.bits()));
            let a_ = a.compact::<LIMBS_2K>(n, K);
            let b_ = b.compact::<LIMBS_2K>(n, K);

            // Compute the K-1 iteration update matrix from a_ and b_
            let (.., matrix, log_upper_bound) = a_
                .to_odd()
                .expect("a is always odd")
                .partial_binxgcd::<LIMBS_K>(&b_, K - 1);

            // Update `a` and `b` using the update matrix
            let (updated_a, updated_b) = matrix.extended_apply_to((a, b));

            (a, _) = updated_a
                .div_2k(log_upper_bound)
                .drop_extension()
                .expect("extension is zero");
            (b, _) = updated_b
                .div_2k(log_upper_bound)
                .drop_extension()
                .expect("extension is zero");
        }

        a.to_odd()
            .expect("gcd of an odd value with something else is always odd")
    }
}

#[cfg(feature = "rand_core")]
#[cfg(test)]
mod tests {

    mod test_bingcd_small {
        use crate::{Gcd, Random, Uint, U1024, U128, U192, U2048, U256, U384, U4096, U512, U64};
        use rand_core::OsRng;

        fn bingcd_small_test<const LIMBS: usize>(lhs: Uint<LIMBS>, rhs: Uint<LIMBS>)
        where
            Uint<LIMBS>: Gcd<Output = Uint<LIMBS>>,
        {
            let gcd = lhs.gcd(&rhs);
            let bingcd = lhs.to_odd().unwrap().bingcd_small(&rhs);
            assert_eq!(gcd, bingcd);
        }

        fn bingcd_small_tests<const LIMBS: usize>()
        where
            Uint<LIMBS>: Gcd<Output = Uint<LIMBS>>,
        {
            // Edge cases
            bingcd_small_test(Uint::ONE, Uint::ZERO);
            bingcd_small_test(Uint::ONE, Uint::ONE);
            bingcd_small_test(Uint::ONE, Uint::MAX);
            bingcd_small_test(Uint::MAX, Uint::ZERO);
            bingcd_small_test(Uint::MAX, Uint::ONE);
            bingcd_small_test(Uint::MAX, Uint::MAX);
            // bingcd_small_test(
            //     Uint::from_be_hex("7BE417F8D79B2A7EAE8E4E9621C36FF3"),
            //     Uint::from_be_hex("02427A8560599FD5183B0375455A895F"),
            // );

            // Randomized test cases
            for _ in 0..100 {
                let x = Uint::<LIMBS>::random(&mut OsRng).bitor(&Uint::ONE);
                let y = Uint::<LIMBS>::random(&mut OsRng);
                bingcd_small_test(x, y);
            }
        }

        #[test]
        fn test_bingcd_small() {
            bingcd_small_tests::<{ U64::LIMBS }>();
            bingcd_small_tests::<{ U128::LIMBS }>();
            bingcd_small_tests::<{ U192::LIMBS }>();
            bingcd_small_tests::<{ U256::LIMBS }>();
            bingcd_small_tests::<{ U384::LIMBS }>();
            bingcd_small_tests::<{ U512::LIMBS }>();
            bingcd_small_tests::<{ U1024::LIMBS }>();
            bingcd_small_tests::<{ U2048::LIMBS }>();
            bingcd_small_tests::<{ U4096::LIMBS }>();
        }
    }

    mod test_bingcd_large {
        use crate::{Gcd, Random, Uint, U1024, U128, U192, U2048, U256, U384, U4096, U512, U64};
        use rand_core::OsRng;

        fn bingcd_large_test<const LIMBS: usize>(lhs: Uint<LIMBS>, rhs: Uint<LIMBS>)
        where
            Uint<LIMBS>: Gcd<Output = Uint<LIMBS>>,
        {
            let gcd = lhs.gcd(&rhs);
            let bingcd = lhs
                .to_odd()
                .unwrap()
                .bingcd_large::<62, { U64::LIMBS }, { U128::LIMBS }>(&rhs);
            assert_eq!(gcd, bingcd);
        }

        fn bingcd_large_tests<const LIMBS: usize>()
        where
            Uint<LIMBS>: Gcd<Output = Uint<LIMBS>>,
        {
            // Edge cases
            bingcd_large_test(Uint::ONE, Uint::ZERO);
            bingcd_large_test(Uint::ONE, Uint::ONE);
            bingcd_large_test(Uint::ONE, Uint::MAX);
            bingcd_large_test(Uint::MAX, Uint::ZERO);
            bingcd_large_test(Uint::MAX, Uint::ONE);
            bingcd_large_test(Uint::MAX, Uint::MAX);
            // bingcd_large_test(
            //     Uint::from_be_hex("7BE417F8D79B2A7EAE8E4E9621C36FF3"),
            //     Uint::from_be_hex("02427A8560599FD5183B0375455A895F"),
            // );

            // Randomized testing
            for _ in 0..100 {
                let x = Uint::<LIMBS>::random(&mut OsRng).bitor(&Uint::ONE);
                let y = Uint::<LIMBS>::random(&mut OsRng);
                bingcd_large_test(x, y);
            }
        }

        #[test]
        fn test_bingcd_large() {
            // Not applicable for U64
            bingcd_large_tests::<{ U128::LIMBS }>();
            bingcd_large_tests::<{ U192::LIMBS }>();
            bingcd_large_tests::<{ U256::LIMBS }>();
            bingcd_large_tests::<{ U384::LIMBS }>();
            bingcd_large_tests::<{ U512::LIMBS }>();
            bingcd_large_tests::<{ U1024::LIMBS }>();
            bingcd_large_tests::<{ U2048::LIMBS }>();
            bingcd_large_tests::<{ U4096::LIMBS }>();
        }
    }
}
