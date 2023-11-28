//! [`BoxedUint`] subtraction operations.

use crate::{BoxedUint, CheckedSub, Limb, Zero};
use subtle::{Choice, CtOption};

impl BoxedUint {
    /// Computes `a + b + carry`, returning the result along with the new carry.
    #[inline(always)]
    pub fn sbb(&self, rhs: &Self, borrow: Limb) -> (Self, Limb) {
        Self::chain(self, rhs, borrow, |a, b, c| a.sbb(b, c))
    }

    /// Perform wrapping subition, discarding overflow.
    pub fn wrapping_sub(&self, rhs: &Self) -> Self {
        self.sbb(rhs, Limb::ZERO).0
    }

    /// Perform wrapping subtraction, returning the truthy value as the second element of the tuple
    /// if an underflow has occurred.
    pub(crate) fn conditional_wrapping_sub(&self, rhs: &Self, choice: Choice) -> (Self, Choice) {
        let actual_rhs = Self::conditional_select(
            &Self::zero_with_precision(rhs.bits_precision()),
            rhs,
            choice,
        );
        let (res, borrow) = self.sbb(&actual_rhs, Limb::ZERO);
        (res, Choice::from((borrow.0 & 1) as u8))
    }
}

impl CheckedSub<&BoxedUint> for BoxedUint {
    type Output = Self;

    fn checked_sub(&self, rhs: &Self) -> CtOption<Self> {
        let (result, carry) = self.sbb(rhs, Limb::ZERO);
        CtOption::new(result, carry.is_zero())
    }
}

#[cfg(test)]
#[allow(clippy::unwrap_used)]
mod tests {
    use super::{BoxedUint, CheckedSub, Limb};

    #[test]
    fn sbb_no_borrow() {
        let (res, carry) = BoxedUint::one().sbb(&BoxedUint::one(), Limb::ZERO);
        assert_eq!(res, BoxedUint::zero());
        assert_eq!(carry, Limb::ZERO);

        let (res, carry) = BoxedUint::one().sbb(&BoxedUint::zero(), Limb::ZERO);
        assert_eq!(res, BoxedUint::one());
        assert_eq!(carry, Limb::ZERO);
    }

    #[test]
    fn sbb_with_borrow() {
        let (res, borrow) = BoxedUint::zero().sbb(&BoxedUint::one(), Limb::ZERO);
        assert_eq!(res, BoxedUint::max(Limb::BITS));
        assert_eq!(borrow, Limb::MAX);
    }

    #[test]
    fn checked_sub_ok() {
        let result = BoxedUint::one().checked_sub(&BoxedUint::one());
        assert_eq!(result.unwrap(), BoxedUint::zero());
    }

    #[test]
    fn checked_sub_overflow() {
        let result = BoxedUint::zero().checked_sub(&BoxedUint::one());
        assert!(!bool::from(result.is_some()));
    }
}
