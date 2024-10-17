//! [`Int`] division operations.

use core::ops::Div;

use subtle::CtOption;

use crate::{CheckedDiv, Int, NonZero};

impl<const LIMBS: usize> Int<LIMBS> {
    /// Perform checked division, returning a [`CtOption`] which `is_some`
    /// only if the rhs != 0
    pub fn checked_div(&self, rhs: &Self) -> CtOption<Self> {
        // Step 1: split operands into signs, magnitudes and whether they are zero.
        let (lhs_sgn, lhs_mag) = self.sign_and_magnitude();
        let (rhs_sgn, rhs_mag) = rhs.sign_and_magnitude();

        // Step 2. Determine if the result should be negated.
        // This should be done if and only if lhs and rhs have opposing signs.
        // Note: if the lhs is zero, the resulting magnitude will also be zero. Negating zero,
        // however, still yields zero, so having a truthy `negate_result` in that scenario is OK.
        let negate_result = lhs_sgn.xor(rhs_sgn);

        // Step 3. Construct result
        lhs_mag
            .checked_div(&rhs_mag)
            .and_then(|magnitude| Self::new_from_sign_and_magnitude(negate_result, magnitude))
    }
}

impl<const LIMBS: usize> CheckedDiv for Int<LIMBS> {
    fn checked_div(&self, rhs: &Int<LIMBS>) -> CtOption<Self> {
        self.checked_div(rhs)
    }
}

impl<const LIMBS: usize> Div<&NonZero<Int<LIMBS>>> for &Int<LIMBS> {
    type Output = CtOption<Int<LIMBS>>;

    fn div(self, rhs: &NonZero<Int<LIMBS>>) -> Self::Output {
        *self / *rhs
    }
}

impl<const LIMBS: usize> Div<&NonZero<Int<LIMBS>>> for Int<LIMBS> {
    type Output = CtOption<Int<LIMBS>>;

    fn div(self, rhs: &NonZero<Int<LIMBS>>) -> Self::Output {
        self / *rhs
    }
}

impl<const LIMBS: usize> Div<NonZero<Int<LIMBS>>> for &Int<LIMBS> {
    type Output = CtOption<Int<LIMBS>>;

    fn div(self, rhs: NonZero<Int<LIMBS>>) -> Self::Output {
        *self / rhs
    }
}

impl<const LIMBS: usize> Div<NonZero<Int<LIMBS>>> for Int<LIMBS> {
    type Output = CtOption<Int<LIMBS>>;

    fn div(self, rhs: NonZero<Int<LIMBS>>) -> Self::Output {
        self.checked_div(&rhs)
    }
}

#[cfg(test)]
mod tests {
    use crate::int::{Int, I128};

    #[test]
    fn test_checked_div() {
        let min_plus_one = Int {
            0: I128::MIN.0.wrapping_add(&I128::ONE.0),
        };

        // lhs = min

        let result = I128::MIN.checked_div(&I128::MIN);
        assert_eq!(result.unwrap(), I128::ONE);

        let result = I128::MIN.checked_div(&I128::MINUS_ONE);
        assert!(bool::from(result.is_none()));

        let result = I128::MIN.checked_div(&I128::ZERO);
        assert!(bool::from(result.is_none()));

        let result = I128::MIN.checked_div(&I128::ONE);
        assert_eq!(result.unwrap(), I128::MIN);

        let result = I128::MIN.checked_div(&I128::MAX);
        assert_eq!(result.unwrap(), I128::MINUS_ONE);

        // lhs = -1

        let result = I128::MINUS_ONE.checked_div(&I128::MIN);
        assert_eq!(result.unwrap(), I128::ZERO);

        let result = I128::MINUS_ONE.checked_div(&I128::MINUS_ONE);
        assert_eq!(result.unwrap(), I128::ONE);

        let result = I128::MINUS_ONE.checked_div(&I128::ZERO);
        assert!(bool::from(result.is_none()));

        let result = I128::MINUS_ONE.checked_div(&I128::ONE);
        assert_eq!(result.unwrap(), I128::MINUS_ONE);

        let result = I128::MINUS_ONE.checked_div(&I128::MAX);
        assert_eq!(result.unwrap(), I128::ZERO);

        // lhs = 0

        let result = I128::ZERO.checked_div(&I128::MIN);
        assert_eq!(result.unwrap(), I128::ZERO);

        let result = I128::ZERO.checked_div(&I128::MINUS_ONE);
        assert_eq!(result.unwrap(), I128::ZERO);

        let result = I128::ZERO.checked_div(&I128::ZERO);
        assert!(bool::from(result.is_none()));

        let result = I128::ZERO.checked_div(&I128::ONE);
        assert_eq!(result.unwrap(), I128::ZERO);

        let result = I128::ZERO.checked_div(&I128::MAX);
        assert_eq!(result.unwrap(), I128::ZERO);

        // lhs = 1

        let result = I128::ONE.checked_div(&I128::MIN);
        assert_eq!(result.unwrap(), I128::ZERO);

        let result = I128::ONE.checked_div(&I128::MINUS_ONE);
        assert_eq!(result.unwrap(), I128::MINUS_ONE);

        let result = I128::ONE.checked_div(&I128::ZERO);
        assert!(bool::from(result.is_none()));

        let result = I128::ONE.checked_div(&I128::ONE);
        assert_eq!(result.unwrap(), I128::ONE);

        let result = I128::ONE.checked_div(&I128::MAX);
        assert_eq!(result.unwrap(), I128::ZERO);

        // lhs = max

        let result = I128::MAX.checked_div(&I128::MIN);
        assert_eq!(result.unwrap(), I128::ZERO);

        let result = I128::MAX.checked_div(&I128::MINUS_ONE);
        assert_eq!(result.unwrap(), min_plus_one);

        let result = I128::MAX.checked_div(&I128::ZERO);
        assert!(bool::from(result.is_none()));

        let result = I128::MAX.checked_div(&I128::ONE);
        assert_eq!(result.unwrap(), I128::MAX);

        let result = I128::MAX.checked_div(&I128::MAX);
        assert_eq!(result.unwrap(), I128::ONE);
    }
}
