//! [`Int`] addition operations.

use core::ops::Add;

use subtle::{Choice, ConstantTimeEq, ConstantTimeGreater, ConstantTimeLess, CtOption};

use crate::{CheckedAdd, CheckedSub, ConstantTimeSelect};
use crate::int::Int;

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

impl<const LIMBS: usize> CheckedAdd for Int<LIMBS> {
    fn checked_add(&self, rhs: &Self) -> CtOption<Self> {
        // Based on the signs of lhs and rhs, we have to consider the following cases:
        // case | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 |
        // -----|---|---|---|---|---|---|---|---|---|
        //  lhs | + | + | + | 0 | 0 | 0 | - | - | - |
        //  rhs | + | 0 | - | + | 0 | - | + | 0 | - |
        //
        // Whether to add or subtract the two halves, which is chosen as follows:
        // case | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 |
        // -----|---|---|---|---|---|---|---|---|---|
        //  a/s | a | a | s | a | a | s | s | s | a |
        //  +/- | + | + | ? | + | + | ? | ? | - | - |

        // One of the two has the result we seek.
        // Now it is a matter of computing which.
        let magnitude_sum = self.magnitude.checked_add(&rhs.magnitude);
        let magnitude_diff = self.magnitude.checked_sub(&rhs.magnitude);

        // Select the magnitude, based on whether lhs and rhs have the same sign.
        let equal_sign = self.is_negative().ct_eq(&rhs.is_negative());
        // Note: we must include the case that either side is ZERO for selecting magnitude_sum
        let use_sum = self.is_zero() | rhs.is_zero() | equal_sign;
        let magnitude = CtOption::ct_select(&magnitude_diff, &magnitude_sum, use_sum);

        // Determine whether the result is negative, based on whether lhs or rhs has a greater magnitude.
        let self_gt_rhs = self.magnitude.ct_gt(&rhs.magnitude);
        let self_lt_rhs = self.magnitude.ct_lt(&rhs.magnitude);
        let is_negative = (self.is_non_negative() | rhs.is_negative() | self_gt_rhs)
            & (self.is_negative() | (rhs.is_negative() & self_lt_rhs));

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
