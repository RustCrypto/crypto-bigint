//! This module implements Least common multiple (LCM) for [`Uint`].

use crate::{ConcatMixed, NonZero, Uint};

impl<const LIMBS: usize> Uint<LIMBS> {
    /// Compute the least common multiple of `self` and `rhs`.
    pub const fn lcm_uint<const WIDE_LIMBS: usize>(&self, rhs: &Self) -> Uint<WIDE_LIMBS>
    where
        Self: ConcatMixed<Uint<LIMBS>, MixedOutput = Uint<WIDE_LIMBS>>,
    {
        let self_is_nz = self.is_nonzero();
        let rhs_is_nz = rhs.is_nonzero();

        let rhs_nz = Uint::select(&Uint::ONE, rhs, rhs_is_nz);

        let gcd_nz = NonZero(self.gcd_uint(&rhs_nz));

        let lcm = self.wrapping_div(&gcd_nz).concatenating_mul(rhs);

        Uint::select(&Uint::ZERO, &lcm, self_is_nz.and(rhs_is_nz))
    }
}

#[cfg(test)]
mod tests {
    mod lcm {
        use crate::{ConcatMixed, U64, U128, U256, U512, U1024, U2048, U4096, Uint};

        fn test<const LIMBS: usize, const WIDE_LIMBS: usize>(
            lhs: Uint<LIMBS>,
            rhs: Uint<LIMBS>,
            target: Uint<WIDE_LIMBS>,
        ) where
            Uint<LIMBS>: ConcatMixed<Uint<LIMBS>, MixedOutput = Uint<WIDE_LIMBS>>,
        {
            assert_eq!(lhs.lcm_uint(&rhs), target);
        }

        fn run_tests<const LIMBS: usize, const WIDE_LIMBS: usize>()
        where
            Uint<LIMBS>: ConcatMixed<Uint<LIMBS>, MixedOutput = Uint<WIDE_LIMBS>>,
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
            run_tests::<{ U64::LIMBS }, _>();
            run_tests::<{ U128::LIMBS }, _>();
            run_tests::<{ U256::LIMBS }, _>();
            run_tests::<{ U512::LIMBS }, _>();
            run_tests::<{ U1024::LIMBS }, _>();
            run_tests::<{ U2048::LIMBS }, _>();
            run_tests::<{ U4096::LIMBS }, _>();
        }
    }
}
