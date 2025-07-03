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
    use crate::{Gcd, I64, I128, I256, I512, I1024, I2048, I4096, Int, Uint};

    fn int_bingcd_test<const LIMBS: usize>(lhs: Int<LIMBS>, rhs: Int<LIMBS>, target: Uint<LIMBS>)
    where
        Uint<LIMBS>: Gcd<Output = Uint<LIMBS>>,
    {
        assert_eq!(lhs.bingcd(&rhs), target);
        assert_eq!(lhs.bingcd_vartime(&rhs), target);
    }

    fn int_bingcd_tests<const LIMBS: usize>()
    where
        Uint<LIMBS>: Gcd<Output = Uint<LIMBS>>,
    {
        let abs_min = *Int::MIN.as_uint();
        let max = *Int::MAX.as_uint();
        int_bingcd_test(Int::MIN, Int::MIN, abs_min);
        int_bingcd_test(Int::MIN, Int::MINUS_ONE, Uint::ONE);
        int_bingcd_test(Int::MIN, Int::ZERO, abs_min);
        int_bingcd_test(Int::MIN, Int::ONE, Uint::ONE);
        int_bingcd_test(Int::MIN, Int::MAX, Uint::ONE);
        int_bingcd_test(Int::MINUS_ONE, Int::MIN, Uint::ONE);
        int_bingcd_test(Int::MINUS_ONE, Int::MINUS_ONE, Uint::ONE);
        int_bingcd_test(Int::MINUS_ONE, Int::ZERO, Uint::ONE);
        int_bingcd_test(Int::MINUS_ONE, Int::ONE, Uint::ONE);
        int_bingcd_test(Int::MINUS_ONE, Int::MAX, Uint::ONE);
        int_bingcd_test(Int::ZERO, Int::MIN, abs_min);
        int_bingcd_test(Int::ZERO, Int::MINUS_ONE, Uint::ONE);
        int_bingcd_test(Int::ZERO, Int::ZERO, Uint::ZERO);
        int_bingcd_test(Int::ZERO, Int::ONE, Uint::ONE);
        int_bingcd_test(Int::ZERO, Int::MAX, max);
        int_bingcd_test(Int::ONE, Int::MIN, Uint::ONE);
        int_bingcd_test(Int::ONE, Int::MINUS_ONE, Uint::ONE);
        int_bingcd_test(Int::ONE, Int::ZERO, Uint::ONE);
        int_bingcd_test(Int::ONE, Int::ONE, Uint::ONE);
        int_bingcd_test(Int::ONE, Int::MAX, Uint::ONE);
        int_bingcd_test(Int::MAX, Int::MIN, Uint::ONE);
        int_bingcd_test(Int::MAX, Int::MINUS_ONE, Uint::ONE);
        int_bingcd_test(Int::MAX, Int::ZERO, max);
        int_bingcd_test(Int::MAX, Int::ONE, Uint::ONE);
        int_bingcd_test(Int::MAX, Int::MAX, max);
    }

    #[test]
    fn test_int_bingcd() {
        int_bingcd_tests::<{ I64::LIMBS }>();
        int_bingcd_tests::<{ I128::LIMBS }>();
        int_bingcd_tests::<{ I256::LIMBS }>();
        int_bingcd_tests::<{ I512::LIMBS }>();
        int_bingcd_tests::<{ I1024::LIMBS }>();
        int_bingcd_tests::<{ I2048::LIMBS }>();
        int_bingcd_tests::<{ I4096::LIMBS }>();
    }
}
