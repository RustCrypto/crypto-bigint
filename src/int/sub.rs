//! [`Int`] subtraction operations.

use core::ops::{Sub, SubAssign};

use subtle::CtOption;

use crate::int::Int;
use crate::{Checked, CheckedAdd, CheckedSub};

impl<const LIMBS: usize> CheckedSub for Int<LIMBS> {
    fn checked_sub(&self, rhs: &Self) -> CtOption<Self> {
        self.checked_add(&rhs.wrapping_neg())
    }
}

impl<const LIMBS: usize> Sub for Int<LIMBS> {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self {
        self.sub(&rhs)
    }
}

impl<const LIMBS: usize> Sub<&Int<LIMBS>> for Int<LIMBS> {
    type Output = Self;

    fn sub(self, rhs: &Self) -> Self {
        self.checked_sub(rhs)
            .expect("attempted to subtract with underflow")
    }
}

impl<const LIMBS: usize> SubAssign for Int<LIMBS> {
    fn sub_assign(&mut self, other: Self) {
        *self -= &other
    }
}

impl<const LIMBS: usize> SubAssign<&Int<LIMBS>> for Int<LIMBS> {
    fn sub_assign(&mut self, other: &Self) {
        *self = *self - other;
    }
}

impl<const LIMBS: usize> SubAssign for Checked<Int<LIMBS>> {
    fn sub_assign(&mut self, other: Self) {
        *self = *self - other;
    }
}

impl<const LIMBS: usize> SubAssign<&Checked<Int<LIMBS>>> for Checked<Int<LIMBS>> {
    fn sub_assign(&mut self, other: &Self) {
        *self = *self - other;
    }
}

#[cfg(test)]
mod tests {
    use crate::int::I128;
    use crate::CheckedSub;

    #[test]
    fn checked_sub_ok() {
        let result = I128::MIN.checked_sub(&I128::MIN);
        assert_eq!(result.unwrap(), I128::ZERO);

        let result = I128::MINUS_ONE.checked_sub(&I128::MINUS_ONE);
        assert_eq!(result.unwrap(), I128::ZERO);

        let result = I128::ZERO.checked_sub(&I128::ZERO);
        assert_eq!(result.unwrap(), I128::ZERO);

        let result = I128::ONE.checked_sub(&I128::ONE);
        assert_eq!(result.unwrap(), I128::ZERO);

        let result = I128::MAX.checked_sub(&I128::MAX);
        assert_eq!(result.unwrap(), I128::ZERO);
    }

    #[test]
    fn checked_sub_overflow() {
        let result = I128::ZERO.checked_sub(&I128::ONE);
        assert!(!bool::from(result.is_some()));
    }
}
