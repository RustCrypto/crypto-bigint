//! This module implements (a constant variant of) the Optimized Extended Binary GCD algorithm,
//! which is described by Pornin in "Optimized Binary GCD for Modular Inversion".
//! Ref: <https://eprint.iacr.org/2020/972.pdf>

use crate::{Int, NonZero, NonZeroUint, Odd, OddUint, Uint};

impl<const LIMBS: usize> Int<LIMBS> {
    /// Compute the gcd of `self` and `rhs` leveraging the Binary GCD algorithm.
    pub const fn bingcd(&self, rhs: &Self) -> Uint<LIMBS> {
        self.abs().bingcd(&rhs.abs())
    }

    /// Compute the gcd of `self` and `rhs` leveraging the Binary GCD algorithm.
    ///
    /// Executes in variable time w.r.t. all input parameters.
    pub const fn bingcd_vartime(&self, rhs: &Self) -> Uint<LIMBS> {
        self.abs().bingcd_vartime(&rhs.abs())
    }
}

impl<const LIMBS: usize> NonZero<Int<LIMBS>> {
    /// Compute the gcd of `self` and `rhs` leveraging the Binary GCD algorithm.
    pub const fn bingcd(&self, rhs: &Self) -> NonZero<Uint<LIMBS>> {
        self.abs().bingcd(&rhs.as_ref().abs())
    }

    /// Compute the gcd of `self` and `rhs` leveraging the Binary GCD algorithm.
    ///
    /// Executes in variable time w.r.t. all input parameters.
    pub const fn bingcd_vartime(&self, rhs: &Self) -> NonZeroUint<LIMBS> {
        self.abs().bingcd_vartime(rhs.abs().as_ref())
    }
}

impl<const LIMBS: usize> Odd<Int<LIMBS>> {
    /// Compute the gcd of `self` and `rhs` leveraging the Binary GCD algorithm.
    pub const fn bingcd(&self, rhs: &Self) -> Odd<Uint<LIMBS>> {
        self.abs().bingcd(&rhs.as_ref().abs())
    }

    /// Compute the gcd of `self` and `rhs` leveraging the Binary GCD algorithm.
    ///
    /// Executes in variable time w.r.t. all input parameters.
    pub const fn bingcd_vartime(&self, rhs: &Self) -> OddUint<LIMBS> {
        self.abs().bingcd_vartime(rhs.abs().as_ref())
    }
}

#[cfg(all(test, not(miri)))]
mod tests {

    mod bingcd {
        use crate::{I64, I128, I256, I512, I1024, I2048, I4096, Int, Uint};

        fn test<const LIMBS: usize>(lhs: Int<LIMBS>, rhs: Int<LIMBS>, target: Uint<LIMBS>) {
            assert_eq!(lhs.bingcd(&rhs), target);
            assert_eq!(lhs.bingcd_vartime(&rhs), target);
        }

        fn run_tests<const LIMBS: usize>() {
            let abs_min = *Int::MIN.as_uint();
            let max = *Int::MAX.as_uint();
            test(Int::<LIMBS>::MIN, Int::MIN, abs_min);
            test(Int::<LIMBS>::MIN, Int::MINUS_ONE, Uint::ONE);
            test(Int::<LIMBS>::MIN, Int::ZERO, abs_min);
            test(Int::<LIMBS>::MIN, Int::ONE, Uint::ONE);
            test(Int::<LIMBS>::MIN, Int::MAX, Uint::ONE);
            test(Int::<LIMBS>::MINUS_ONE, Int::MIN, Uint::ONE);
            test(Int::<LIMBS>::MINUS_ONE, Int::MINUS_ONE, Uint::ONE);
            test(Int::<LIMBS>::MINUS_ONE, Int::ZERO, Uint::ONE);
            test(Int::<LIMBS>::MINUS_ONE, Int::ONE, Uint::ONE);
            test(Int::<LIMBS>::MINUS_ONE, Int::MAX, Uint::ONE);
            test(Int::<LIMBS>::ZERO, Int::MIN, abs_min);
            test(Int::<LIMBS>::ZERO, Int::MINUS_ONE, Uint::ONE);
            test(Int::<LIMBS>::ZERO, Int::ZERO, Uint::ZERO);
            test(Int::<LIMBS>::ZERO, Int::ONE, Uint::ONE);
            test(Int::<LIMBS>::ZERO, Int::MAX, max);
            test(Int::<LIMBS>::ONE, Int::MIN, Uint::ONE);
            test(Int::<LIMBS>::ONE, Int::MINUS_ONE, Uint::ONE);
            test(Int::<LIMBS>::ONE, Int::ZERO, Uint::ONE);
            test(Int::<LIMBS>::ONE, Int::ONE, Uint::ONE);
            test(Int::<LIMBS>::ONE, Int::MAX, Uint::ONE);
            test(Int::<LIMBS>::MAX, Int::MIN, Uint::ONE);
            test(Int::<LIMBS>::MAX, Int::MINUS_ONE, Uint::ONE);
            test(Int::<LIMBS>::MAX, Int::ZERO, max);
            test(Int::<LIMBS>::MAX, Int::ONE, Uint::ONE);
            test(Int::<LIMBS>::MAX, Int::MAX, max);
        }

        #[test]
        fn bingcd() {
            run_tests::<{ I64::LIMBS }>();
            run_tests::<{ I128::LIMBS }>();
            run_tests::<{ I256::LIMBS }>();
            run_tests::<{ I512::LIMBS }>();
            run_tests::<{ I1024::LIMBS }>();
            run_tests::<{ I2048::LIMBS }>();
            run_tests::<{ I4096::LIMBS }>();
        }
    }
}
