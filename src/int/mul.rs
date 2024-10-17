//! [`Int`] multiplication operations.

use core::ops::{Mul, MulAssign};

use subtle::CtOption;

use crate::{Checked, CheckedMul, ConstChoice, Int, Uint, Zero};

impl<const LIMBS: usize> Int<LIMBS> {
    /// Compute "wide" multiplication as a 3-tuple `(lo, hi, negate)`.
    /// The `(lo, hi)` components contain the _magnitude of the product_, with sizes
    /// corresponding to the sizes of the operands; `negate` indicates whether the result should be
    /// negated when converted from `Uint` to `Int`. Note: even if `negate` is truthy, the magnitude
    /// might be zero!
    pub const fn split_mul<const RHS_LIMBS: usize>(
        &self,
        rhs: &Int<RHS_LIMBS>,
    ) -> (Uint<{ LIMBS }>, Uint<{ RHS_LIMBS }>, ConstChoice) {
        // Step 1: split operands into their signs and magnitudes.
        let (lhs_sgn, lhs_mag) = self.sign_and_magnitude();
        let (rhs_sgn, rhs_mag) = rhs.sign_and_magnitude();

        // Step 2: multiply the magnitudes
        let (lo, hi) = lhs_mag.split_mul(&rhs_mag);

        // Step 3. Determine if the result should be negated.
        // This should be done if and only if lhs and rhs have opposing signs.
        // Note: if either operand is zero, the resulting magnitude will also be zero. Negating
        // zero, however, still yields zero, so having a truthy `negate` in that scenario is OK.
        let negate = lhs_sgn.xor(rhs_sgn);

        (lo, hi, negate)
    }
}

impl<const LIMBS: usize, const RHS_LIMBS: usize> CheckedMul<Int<RHS_LIMBS>> for Int<LIMBS> {
    #[inline]
    fn checked_mul(&self, rhs: &Int<RHS_LIMBS>) -> CtOption<Self> {
        let (lo, hi, is_negative) = self.split_mul(rhs);
        let val = Self::new_from_sign_and_magnitude(is_negative, lo);
        val.and_then(|int| CtOption::new(int, hi.is_zero()))
    }
}

impl<const LIMBS: usize, const RHS_LIMBS: usize> Mul<Int<RHS_LIMBS>> for Int<LIMBS> {
    type Output = Int<LIMBS>;

    fn mul(self, rhs: Int<RHS_LIMBS>) -> Self {
        self.mul(&rhs)
    }
}

impl<const LIMBS: usize, const RHS_LIMBS: usize> Mul<&Int<RHS_LIMBS>> for Int<LIMBS> {
    type Output = Int<LIMBS>;

    fn mul(self, rhs: &Int<RHS_LIMBS>) -> Self {
        (&self).mul(rhs)
    }
}

impl<const LIMBS: usize, const RHS_LIMBS: usize> Mul<Int<RHS_LIMBS>> for &Int<LIMBS> {
    type Output = Int<LIMBS>;

    fn mul(self, rhs: Int<RHS_LIMBS>) -> Self::Output {
        self.mul(&rhs)
    }
}

impl<const LIMBS: usize, const RHS_LIMBS: usize> Mul<&Int<RHS_LIMBS>> for &Int<LIMBS> {
    type Output = Int<LIMBS>;

    fn mul(self, rhs: &Int<RHS_LIMBS>) -> Self::Output {
        self.checked_mul(rhs)
            .expect("attempted to multiply with overflow")
    }
}

impl<const LIMBS: usize> MulAssign<Checked<Int<LIMBS>>> for Checked<Int<LIMBS>> {
    fn mul_assign(&mut self, other: Checked<Int<LIMBS>>) {
        *self = *self * other;
    }
}

impl<const LIMBS: usize> MulAssign<&Checked<Int<LIMBS>>> for Checked<Int<LIMBS>> {
    fn mul_assign(&mut self, other: &Checked<Int<LIMBS>>) {
        *self = *self * other;
    }
}

#[cfg(test)]
mod tests {
    use crate::int::{Int, I128};
    use crate::CheckedMul;

    #[test]
    fn test_checked_mul() {
        let min_plus_one = Int {
            0: I128::MIN.0.wrapping_add(&I128::ONE.0),
        };

        // lhs = min

        let result = I128::MIN.checked_mul(&I128::MIN);
        assert!(bool::from(result.is_none()));

        let result = I128::MIN.checked_mul(&I128::MINUS_ONE);
        assert!(bool::from(result.is_none()));

        let result = I128::MIN.checked_mul(&I128::ZERO);
        assert_eq!(result.unwrap(), I128::ZERO);

        let result = I128::MIN.checked_mul(&I128::ONE);
        assert_eq!(result.unwrap(), I128::MIN);

        let result = I128::MIN.checked_mul(&I128::MAX);
        assert!(bool::from(result.is_none()));

        // lhs = -1

        let result = I128::MINUS_ONE.checked_mul(&I128::MIN);
        assert!(bool::from(result.is_none()));

        let result = I128::MINUS_ONE.checked_mul(&I128::MINUS_ONE);
        assert_eq!(result.unwrap(), I128::ONE);

        let result = I128::MINUS_ONE.checked_mul(&I128::ZERO);
        assert_eq!(result.unwrap(), I128::ZERO);

        let result = I128::MINUS_ONE.checked_mul(&I128::ONE);
        assert_eq!(result.unwrap(), I128::MINUS_ONE);

        let result = I128::MINUS_ONE.checked_mul(&I128::MAX);
        assert_eq!(result.unwrap(), min_plus_one);

        // lhs = 0

        let result = I128::ZERO.checked_mul(&I128::MIN);
        assert_eq!(result.unwrap(), I128::ZERO);

        let result = I128::ZERO.checked_mul(&I128::MINUS_ONE);
        assert_eq!(result.unwrap(), I128::ZERO);

        let result = I128::ZERO.checked_mul(&I128::ZERO);
        assert_eq!(result.unwrap(), I128::ZERO);

        let result = I128::ZERO.checked_mul(&I128::ONE);
        assert_eq!(result.unwrap(), I128::ZERO);

        let result = I128::ZERO.checked_mul(&I128::MAX);
        assert_eq!(result.unwrap(), I128::ZERO);

        // lhs = 1

        let result = I128::ONE.checked_mul(&I128::MIN);
        assert_eq!(result.unwrap(), I128::MIN);

        let result = I128::ONE.checked_mul(&I128::MINUS_ONE);
        assert_eq!(result.unwrap(), I128::MINUS_ONE);

        let result = I128::ONE.checked_mul(&I128::ZERO);
        assert_eq!(result.unwrap(), I128::ZERO);

        let result = I128::ONE.checked_mul(&I128::ONE);
        assert_eq!(result.unwrap(), I128::ONE);

        let result = I128::ONE.checked_mul(&I128::MAX);
        assert_eq!(result.unwrap(), I128::MAX);

        // lhs = max

        let result = I128::MAX.checked_mul(&I128::MIN);
        assert!(bool::from(result.is_none()));

        let result = I128::MAX.checked_mul(&I128::MINUS_ONE);
        assert_eq!(result.unwrap(), min_plus_one);

        let result = I128::MAX.checked_mul(&I128::ZERO);
        assert_eq!(result.unwrap(), I128::ZERO);

        let result = I128::MAX.checked_mul(&I128::ONE);
        assert_eq!(result.unwrap(), I128::MAX);

        let result = I128::MAX.checked_mul(&I128::MAX);
        assert!(bool::from(result.is_none()));
    }
}
