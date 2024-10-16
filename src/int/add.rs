//! [`Int`] addition operations.

use core::ops::{Add, AddAssign};

use num_traits::WrappingAdd;
use subtle::{ConstantTimeEq, CtOption};

use crate::{Checked, CheckedAdd, Int, Wrapping};

impl<const LIMBS: usize> Int<LIMBS> {
    /// Perform checked addition.
    fn checked_add_internal(&self, rhs: &Self) -> CtOption<Self> {
        // Step 1. add operands
        let res = Self(self.0.wrapping_add(&rhs.0));

        // Step 2. check whether overflow happened.
        // Note:
        // - overflow can only happen when the inputs have the same sign, and then
        // - overflow occurs if and only if the result has the opposite sign of both inputs.
        //
        // We can thus express the overflow flag as: (self.msb == rhs.msb) & (self.msb != res.msb)
        let self_msb = self.sign_bit();
        let overflow = self_msb.ct_eq(&rhs.sign_bit()) & self_msb.ct_ne(&res.sign_bit());

        // Step 3. Construct result
        CtOption::new(res, !overflow)
    }

    /// Perform wrapping addition, discarding overflow.
    pub const fn wrapping_add(&self, rhs: &Self) -> Self {
        Self(self.0.wrapping_add(&rhs.0))
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
    fn add_assign(&mut self, other: Self) {
        *self += &other;
    }
}

impl<const LIMBS: usize> AddAssign<&Int<LIMBS>> for Int<LIMBS> {
    fn add_assign(&mut self, other: &Self) {
        *self = *self + other;
    }
}

impl<const LIMBS: usize> AddAssign for Wrapping<Int<LIMBS>> {
    fn add_assign(&mut self, other: Self) {
        *self = *self + other;
    }
}

impl<const LIMBS: usize> AddAssign<&Wrapping<Int<LIMBS>>> for Wrapping<Int<LIMBS>> {
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
    fn checked_add(&self, rhs: &Self) -> CtOption<Self> {
        self.checked_add_internal(rhs)
    }
}

impl<const LIMBS: usize> WrappingAdd for Int<LIMBS> {
    fn wrapping_add(&self, v: &Self) -> Self {
        self.wrapping_add(v)
    }
}

#[cfg(test)]
mod tests {

    #[cfg(test)]
    mod tests {
        use crate::int::I128;
        use crate::{CheckedAdd, Int, U128};

        #[test]
        fn checked_add() {
            let min_plus_one = Int {
                0: I128::MIN.0.wrapping_add(&I128::ONE.0),
            };
            let max_minus_one = Int {
                0: I128::MAX.0.wrapping_sub(&I128::ONE.0),
            };
            let two = Int {
                0: U128::from(2u32),
            };

            // lhs = MIN

            let result = I128::MIN.checked_add(&I128::MIN);
            assert!(bool::from(result.is_none()));

            let result = I128::MIN.checked_add(&I128::MINUS_ONE);
            assert!(bool::from(result.is_none()));

            let result = I128::MIN.checked_add(&I128::ZERO);
            assert_eq!(result.unwrap(), I128::MIN);

            let result = I128::MIN.checked_add(&I128::ONE);
            assert_eq!(result.unwrap(), min_plus_one);

            let result = I128::MIN.checked_add(&I128::MAX);
            assert_eq!(result.unwrap(), I128::MINUS_ONE);

            // lhs = -1

            let result = I128::MINUS_ONE.checked_add(&I128::MIN);
            assert!(bool::from(result.is_none()));

            let result = I128::MINUS_ONE.checked_add(&I128::MINUS_ONE);
            assert_eq!(result.unwrap(), two.neg().unwrap());

            let result = I128::MINUS_ONE.checked_add(&I128::ZERO);
            assert_eq!(result.unwrap(), I128::MINUS_ONE);

            let result = I128::MINUS_ONE.checked_add(&I128::ONE);
            assert_eq!(result.unwrap(), I128::ZERO);

            let result = I128::MINUS_ONE.checked_add(&I128::MAX);
            assert_eq!(result.unwrap(), max_minus_one);

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
            assert_eq!(result.unwrap(), min_plus_one);

            let result = I128::ONE.checked_add(&I128::MINUS_ONE);
            assert_eq!(result.unwrap(), I128::ZERO);

            let result = I128::ONE.checked_add(&I128::ZERO);
            assert_eq!(result.unwrap(), I128::ONE);

            let result = I128::ONE.checked_add(&I128::ONE);
            assert_eq!(result.unwrap(), two);

            let result = I128::ONE.checked_add(&I128::MAX);
            assert!(bool::from(result.is_none()));

            // lhs = MAX

            let result = I128::MAX.checked_add(&I128::MIN);
            assert_eq!(result.unwrap(), I128::MINUS_ONE);

            let result = I128::MAX.checked_add(&I128::MINUS_ONE);
            assert_eq!(result.unwrap(), max_minus_one);

            let result = I128::MAX.checked_add(&I128::ZERO);
            assert_eq!(result.unwrap(), I128::MAX);

            let result = I128::MAX.checked_add(&I128::ONE);
            assert!(bool::from(result.is_none()));

            let result = I128::MAX.checked_add(&I128::MAX);
            assert!(bool::from(result.is_none()));
        }
    }
}
