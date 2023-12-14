//! [`BoxedUint`] subtraction operations.

use crate::{BoxedUint, CheckedSub, Limb, Wrapping, Zero};
use core::ops::SubAssign;
use subtle::{Choice, ConditionallySelectable, CtOption};

impl BoxedUint {
    /// Computes `a - (b + borrow)`, returning the result along with the new borrow.
    #[inline(always)]
    pub fn sbb(&self, rhs: &Self, borrow: Limb) -> (Self, Limb) {
        Self::fold_limbs(self, rhs, borrow, |a, b, c| a.sbb(b, c))
    }

    /// Computes `a - (b + borrow)` in-place, returning the new borrow.
    ///
    /// Panics if `rhs` has a larger precision than `self`.
    #[inline(always)]
    pub fn sbb_assign(&mut self, rhs: &Self, mut borrow: Limb) -> Limb {
        debug_assert!(self.bits_precision() <= rhs.bits_precision());

        for i in 0..self.nlimbs() {
            let (limb, b) = self.limbs[i].sbb(*rhs.limbs.get(i).unwrap_or(&Limb::ZERO), borrow);
            self.limbs[i] = limb;
            borrow = b;
        }

        borrow
    }

    /// Perform wrapping subtraction, discarding overflow.
    pub fn wrapping_sub(&self, rhs: &Self) -> Self {
        self.sbb(rhs, Limb::ZERO).0
    }

    /// Perform in-place wrapping subtraction, returning the truthy value as the second element of
    /// the tuple if an underflow has occurred.
    pub(crate) fn conditional_sbb_assign(&mut self, rhs: &Self, choice: Choice) -> Choice {
        debug_assert!(self.bits_precision() <= rhs.bits_precision());
        let mask = Limb::conditional_select(&Limb::ZERO, &Limb::MAX, choice);
        let mut borrow = Limb::ZERO;

        for i in 0..self.nlimbs() {
            let masked_rhs = *rhs.limbs.get(i).unwrap_or(&Limb::ZERO) & mask;
            let (limb, b) = self.limbs[i].sbb(masked_rhs, borrow);
            self.limbs[i] = limb;
            borrow = b;
        }

        Choice::from((borrow.0 & 1) as u8)
    }
}

impl CheckedSub<&BoxedUint> for BoxedUint {
    type Output = Self;

    fn checked_sub(&self, rhs: &Self) -> CtOption<Self> {
        let (result, carry) = self.sbb(rhs, Limb::ZERO);
        CtOption::new(result, carry.is_zero())
    }
}

impl SubAssign<Wrapping<BoxedUint>> for Wrapping<BoxedUint> {
    fn sub_assign(&mut self, other: Wrapping<BoxedUint>) {
        self.0.sbb_assign(&other.0, Limb::ZERO);
    }
}

impl SubAssign<&Wrapping<BoxedUint>> for Wrapping<BoxedUint> {
    fn sub_assign(&mut self, other: &Wrapping<BoxedUint>) {
        self.0.sbb_assign(&other.0, Limb::ZERO);
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
