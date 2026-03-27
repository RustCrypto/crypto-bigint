//! This module implements Least common multiple (LCM) for [`Uint`].

use crate::{Concat, Uint};

impl<const LIMBS: usize> Uint<LIMBS> {
    /// Compute the least common multiple of `self` and `rhs`.
    #[must_use]
    pub const fn lcm<const WIDE_LIMBS: usize>(&self, rhs: &Self) -> Uint<WIDE_LIMBS>
    where
        Self: Concat<LIMBS, Output = Uint<WIDE_LIMBS>>,
    {
        let (lhs_nz, _) = self.to_nz_or_one();
        let gcd_nz = lhs_nz.gcd_unsigned(rhs);
        self.wrapping_div(&gcd_nz).concatenating_mul(rhs)
    }
}

#[cfg(test)]
mod tests {
    mod lcm {
        use crate::{Concat, U64, U128, U256, U512, U1024, U2048, U4096, U8192, Uint};

        fn test<const LIMBS: usize, const WIDE_LIMBS: usize>(
            lhs: Uint<LIMBS>,
            rhs: Uint<LIMBS>,
            target: Uint<WIDE_LIMBS>,
        ) where
            Uint<LIMBS>: Concat<LIMBS, Output = Uint<WIDE_LIMBS>>,
        {
            assert_eq!(lhs.lcm(&rhs), target);
        }

        fn run_tests<const LIMBS: usize, const WIDE_LIMBS: usize>()
        where
            Uint<LIMBS>: Concat<LIMBS, Output = Uint<WIDE_LIMBS>>,
        {
            test(Uint::<LIMBS>::ZERO, Uint::ZERO, Uint::<WIDE_LIMBS>::ZERO);
            test(Uint::<LIMBS>::ZERO, Uint::ONE, Uint::<WIDE_LIMBS>::ZERO);
            test(Uint::<LIMBS>::ZERO, Uint::MAX, Uint::<WIDE_LIMBS>::ZERO);
            test(Uint::<LIMBS>::ONE, Uint::ZERO, Uint::<WIDE_LIMBS>::ZERO);
            test(Uint::<LIMBS>::ONE, Uint::ONE, Uint::<WIDE_LIMBS>::ONE);
            test(
                Uint::<LIMBS>::ONE,
                Uint::MAX,
                Uint::<LIMBS>::MAX.resize::<WIDE_LIMBS>(),
            );
            test(Uint::<LIMBS>::MAX, Uint::ZERO, Uint::<WIDE_LIMBS>::ZERO);
            test(
                Uint::<LIMBS>::MAX,
                Uint::ONE,
                Uint::<LIMBS>::MAX.resize::<WIDE_LIMBS>(),
            );
            test(
                Uint::<LIMBS>::MAX,
                Uint::MAX,
                Uint::<LIMBS>::MAX.resize::<WIDE_LIMBS>(),
            );
        }

        #[test]
        fn lcm_sizes() {
            run_tests::<{ U64::LIMBS }, { U128::LIMBS }>();
            run_tests::<{ U128::LIMBS }, { U256::LIMBS }>();
            run_tests::<{ U256::LIMBS }, { U512::LIMBS }>();
            run_tests::<{ U512::LIMBS }, { U1024::LIMBS }>();
            if cfg!(not(miri)) {
                run_tests::<{ U1024::LIMBS }, { U2048::LIMBS }>();
                run_tests::<{ U2048::LIMBS }, { U4096::LIMBS }>();
                run_tests::<{ U4096::LIMBS }, { U8192::LIMBS }>();
            }
        }
    }
}
