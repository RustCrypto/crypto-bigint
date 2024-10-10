//! [`Int`] addition operations.

use core::ops::{Add, AddAssign};

use subtle::{Choice, ConstantTimeEq, ConstantTimeLess, CtOption};

use crate::{Checked, CheckedAdd, CheckedSub, ConstantTimeSelect, Uint};
use crate::int::Int;

impl<const LIMBS: usize> Int<LIMBS> {
    /// Add two [`Int`]s, checking for overflow.
    ///
    /// Assumes `self.magnitude >= rhs.magnitude`.
    fn checked_adc(&self, rhs: &Self) -> CtOption<Self> {
        // Step 1. Add/subtract the magnitudes of the two sides to/from each other
        let magnitude_add = self.magnitude.checked_add(&rhs.magnitude);
        let magnitude_sub = self.magnitude.checked_sub(&rhs.magnitude);

        // Step 2. Select magnitude_sub when the signs of the two elements are not the same.
        let different_signs = self.is_negative().ct_ne(&rhs.is_negative());
        let magnitude = CtOption::ct_select(&magnitude_add, &magnitude_sub, different_signs);

        // Step 3. Determine the sign of the result.
        // This is always the same as the sign of the self (since it assumed to have the
        // larger magnitude), except when the sum is zero.
        let sum_is_zero = different_signs & self.magnitude.ct_eq(&rhs.magnitude);
        let is_negative = self.is_negative() & !sum_is_zero;

        magnitude.and_then(|magnitude| {
            CtOption::new(
                Self {
                    is_negative: is_negative.unwrap_u8() == 1,
                    magnitude,
                },
                Choice::from(1),
            )
        })
    }
}

impl<const LIMBS: usize> Add for Int<LIMBS> {
    type Output = Self;

    fn add(self, rhs: Self) -> Self {
        self.add(&rhs)
    }
}

impl<const LIMBS: usize> Add<&Int<LIMBS>> for Int<LIMBS> {
    type Output = Self;

    fn add(self, rhs: &Self) -> Self {
        self.checked_add(rhs)
            .expect("attempted to add with overflow")
    }
}

impl<const LIMBS: usize> AddAssign for Int<LIMBS> {
    fn add_assign(&mut self, mut rhs: Self) {
        // Order the elements, such that |lhs| >= |rhs|
        let self_lt_other = self.magnitude.ct_lt(&rhs.magnitude);
        Uint::ct_swap(&mut self.magnitude, &mut rhs.magnitude, self_lt_other);

        *self = self
            .checked_adc(&rhs)
            .expect("attempted to add with overflow");
    }
}

impl<const LIMBS: usize> AddAssign<&Int<LIMBS>> for Int<LIMBS> {
    fn add_assign(&mut self, other: &Self) {
        *self = *self + other;
    }
}

impl<const LIMBS: usize> AddAssign for Checked<Int<LIMBS>> {
    fn add_assign(&mut self, other: Self) {
        *self = *self + other;
    }
}

impl<const LIMBS: usize> AddAssign<&Checked<Int<LIMBS>>> for Checked<Int<LIMBS>> {
    fn add_assign(&mut self, other: &Self) {
        *self = *self + other;
    }
}

impl<const LIMBS: usize> CheckedAdd for Int<LIMBS> {
    /// Add two [`Int`]s, checking for overflow.
    fn checked_add(&self, rhs: &Self) -> CtOption<Self> {
        // Select the element with the largest magnitude to be the lhs.
        let (lhs, rhs) = Int::abs_max_min(self, rhs);
        lhs.checked_adc(&rhs)
    }
}

#[cfg(test)]
mod tests {
    use crate::{CheckedAdd, U128};
    use crate::int::I128;

    #[test]
    fn checked_add() {
        let max_minus_one = U128::MAX.wrapping_sub(&U128::ONE);
        let two = U128::from(2u32);

        // lhs = MIN

        let result = I128::MIN.checked_add(&I128::MIN);
        assert!(bool::from(result.is_none()));

        let result = I128::MIN.checked_add(&I128::MINUS_ONE);
        assert!(bool::from(result.is_none()));

        let result = I128::MIN.checked_add(&I128::ZERO);
        assert_eq!(result.unwrap(), I128::MIN);

        let result = I128::MIN.checked_add(&I128::ONE);
        assert_eq!(result.unwrap(), I128::new_from_uint(true, max_minus_one));

        let result = I128::MIN.checked_add(&I128::MAX);
        assert_eq!(result.unwrap(), I128::ZERO);

        // lhs = -1

        let result = I128::MINUS_ONE.checked_add(&I128::MIN);
        assert!(bool::from(result.is_none()));

        let result = I128::MINUS_ONE.checked_add(&I128::MINUS_ONE);
        assert_eq!(result.unwrap(), I128::new_from_uint(true, two));

        let result = I128::MINUS_ONE.checked_add(&I128::ZERO);
        assert_eq!(result.unwrap(), I128::MINUS_ONE);

        let result = I128::MINUS_ONE.checked_add(&I128::ONE);
        assert_eq!(result.unwrap(), I128::ZERO);

        let result = I128::MINUS_ONE.checked_add(&I128::MAX);
        assert_eq!(result.unwrap(), I128::new_from_uint(false, max_minus_one));

        // lhs = 0

        let result = I128::ZERO.checked_add(&I128::MIN);
        assert_eq!(result.unwrap(), I128::MIN);

        let result = I128::ZERO.checked_add(&I128::MINUS_ONE);
        assert_eq!(result.unwrap(), I128::MINUS_ONE);

        let result = I128::ZERO.checked_add(&I128::ZERO);
        assert_eq!(result.unwrap(), I128::ZERO);

        let result = I128::ZERO.checked_add(&I128::ONE);
        assert_eq!(result.unwrap(), I128::ONE);

        let result = I128::ZERO.checked_add(&I128::MAX);
        assert_eq!(result.unwrap(), I128::MAX);

        // lhs = 1

        let result = I128::ONE.checked_add(&I128::MIN);
        assert_eq!(result.unwrap(), I128::new_from_uint(true, max_minus_one));

        let result = I128::ONE.checked_add(&I128::MINUS_ONE);
        assert_eq!(result.unwrap(), I128::ZERO);

        let result = I128::ONE.checked_add(&I128::ZERO);
        assert_eq!(result.unwrap(), I128::ONE);

        let result = I128::ONE.checked_add(&I128::ONE);
        assert_eq!(result.unwrap(), I128::new_from_uint(false, two));

        let result = I128::ONE.checked_add(&I128::MAX);
        assert!(bool::from(result.is_none()));

        // lhs = MAX

        let result = I128::MAX.checked_add(&I128::MIN);
        assert_eq!(result.unwrap(), I128::ZERO);

        let result = I128::MAX.checked_add(&I128::MINUS_ONE);
        assert_eq!(result.unwrap(), I128::new_from_uint(false, max_minus_one));

        let result = I128::MAX.checked_add(&I128::ZERO);
        assert_eq!(result.unwrap(), I128::MAX);

        let result = I128::MAX.checked_add(&I128::ONE);
        assert!(bool::from(result.is_none()));

        let result = I128::MAX.checked_add(&I128::MAX);
        assert!(bool::from(result.is_none()));
    }
}
