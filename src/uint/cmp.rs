//! [`Uint`] comparisons.
//!
//! By default these are all constant-time and use the `subtle` crate.

use super::Uint;
use crate::{CtChoice, Limb, Word};
use core::cmp::Ordering;
use subtle::{Choice, ConstantTimeEq, ConstantTimeGreater, ConstantTimeLess};

impl<const LIMBS: usize> Uint<LIMBS> {
    /// Return `b` if `c` is truthy, otherwise return `a`.
    #[inline]
    pub(crate) const fn ct_select(a: Uint<LIMBS>, b: Uint<LIMBS>, c: CtChoice) -> Self {
        let mut limbs = [Limb::ZERO; LIMBS];

        let mut i = 0;
        while i < LIMBS {
            limbs[i] = Limb::ct_select(a.limbs[i], b.limbs[i], c);
            i += 1;
        }

        Uint { limbs }
    }

    #[inline]
    pub(crate) const fn ct_swap(a: Uint<LIMBS>, b: Uint<LIMBS>, c: CtChoice) -> (Self, Self) {
        let new_a = Self::ct_select(a, b, c);
        let new_b = Self::ct_select(b, a, c);

        (new_a, new_b)
    }

    /// Returns the truthy value if `self`!=0 or the falsy value otherwise.
    #[inline]
    pub(crate) const fn ct_is_nonzero(&self) -> CtChoice {
        let mut b = 0;
        let mut i = 0;
        while i < LIMBS {
            b |= self.limbs[i].0;
            i += 1;
        }
        Limb(b).ct_is_nonzero()
    }

    /// Returns the truthy value if `self` is odd or the falsy value otherwise.
    pub(crate) const fn ct_is_odd(&self) -> CtChoice {
        (self.limbs[0].0 & 1).wrapping_neg()
    }

    /// Returns the truthy value if `self == rhs` or the falsy value otherwise.
    #[inline]
    pub(crate) const fn ct_eq(&self, rhs: &Self) -> CtChoice {
        let mut acc = 0;
        let mut i = 0;

        while i < LIMBS {
            acc |= self.limbs[i].0 ^ rhs.limbs[i].0;
            i += 1;
        }

        // acc == 0 if and only if self == rhs
        !Limb(acc).ct_is_nonzero()
    }

    /// Returns the truthy value if `self <= rhs` and the falsy value otherwise.
    #[inline]
    pub(crate) const fn ct_lt(&self, rhs: &Self) -> CtChoice {
        // We could use the same approach as in Limb::ct_lt(),
        // but since we have to use Uint::wrapping_sub(), which calls `sbb()`,
        // there are no savings compared to just calling `sbb()` directly.
        let (_res, borrow) = self.sbb(rhs, Limb::ZERO);
        borrow.0
    }

    /// Returns the truthy value if `self <= rhs` and the falsy value otherwise.
    #[inline]
    pub(crate) const fn ct_gt(&self, rhs: &Self) -> CtChoice {
        let (_res, borrow) = rhs.sbb(self, Limb::ZERO);
        borrow.0
    }
}

impl<const LIMBS: usize> ConstantTimeEq for Uint<LIMBS> {
    #[inline]
    fn ct_eq(&self, other: &Self) -> Choice {
        Choice::from(self.ct_eq(other) as u8 & 1)
    }
}

impl<const LIMBS: usize> ConstantTimeGreater for Uint<LIMBS> {
    #[inline]
    fn ct_gt(&self, other: &Self) -> Choice {
        Choice::from(self.ct_gt(other) as u8 & 1)
    }
}

impl<const LIMBS: usize> ConstantTimeLess for Uint<LIMBS> {
    #[inline]
    fn ct_lt(&self, other: &Self) -> Choice {
        Choice::from(self.ct_lt(other) as u8 & 1)
    }
}

impl<const LIMBS: usize> Eq for Uint<LIMBS> {}

impl<const LIMBS: usize> Ord for Uint<LIMBS> {
    fn cmp(&self, other: &Self) -> Ordering {
        let is_lt = self.ct_lt(other);
        let is_eq = self.ct_eq(other);

        if is_lt == Word::MAX {
            Ordering::Less
        } else if is_eq == Word::MAX {
            Ordering::Equal
        } else {
            Ordering::Greater
        }
    }
}

impl<const LIMBS: usize> PartialOrd for Uint<LIMBS> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<const LIMBS: usize> PartialEq for Uint<LIMBS> {
    fn eq(&self, other: &Self) -> bool {
        self.ct_eq(other) == Word::MAX
    }
}

#[cfg(test)]
mod tests {
    use crate::{Integer, Zero, U128};
    use subtle::{ConstantTimeEq, ConstantTimeGreater, ConstantTimeLess};

    #[test]
    fn is_zero() {
        assert!(bool::from(U128::ZERO.is_zero()));
        assert!(!bool::from(U128::ONE.is_zero()));
        assert!(!bool::from(U128::MAX.is_zero()));
    }

    #[test]
    fn is_odd() {
        assert!(!bool::from(U128::ZERO.is_odd()));
        assert!(bool::from(U128::ONE.is_odd()));
        assert!(bool::from(U128::MAX.is_odd()));
    }

    #[test]
    fn ct_eq() {
        let a = U128::ZERO;
        let b = U128::MAX;

        assert!(bool::from(ConstantTimeEq::ct_eq(&a, &a)));
        assert!(!bool::from(ConstantTimeEq::ct_eq(&a, &b)));
        assert!(!bool::from(ConstantTimeEq::ct_eq(&b, &a)));
        assert!(bool::from(ConstantTimeEq::ct_eq(&b, &b)));
    }

    #[test]
    fn ct_gt() {
        let a = U128::ZERO;
        let b = U128::ONE;
        let c = U128::MAX;

        assert!(bool::from(ConstantTimeGreater::ct_gt(&b, &a)));
        assert!(bool::from(ConstantTimeGreater::ct_gt(&c, &a)));
        assert!(bool::from(ConstantTimeGreater::ct_gt(&c, &b)));

        assert!(!bool::from(ConstantTimeGreater::ct_gt(&a, &a)));
        assert!(!bool::from(ConstantTimeGreater::ct_gt(&b, &b)));
        assert!(!bool::from(ConstantTimeGreater::ct_gt(&c, &c)));

        assert!(!bool::from(ConstantTimeGreater::ct_gt(&a, &b)));
        assert!(!bool::from(ConstantTimeGreater::ct_gt(&a, &c)));
        assert!(!bool::from(ConstantTimeGreater::ct_gt(&b, &c)));
    }

    #[test]
    fn ct_lt() {
        let a = U128::ZERO;
        let b = U128::ONE;
        let c = U128::MAX;

        assert!(bool::from(ConstantTimeLess::ct_lt(&a, &b)));
        assert!(bool::from(ConstantTimeLess::ct_lt(&a, &c)));
        assert!(bool::from(ConstantTimeLess::ct_lt(&b, &c)));

        assert!(!bool::from(ConstantTimeLess::ct_lt(&a, &a)));
        assert!(!bool::from(ConstantTimeLess::ct_lt(&b, &b)));
        assert!(!bool::from(ConstantTimeLess::ct_lt(&c, &c)));

        assert!(!bool::from(ConstantTimeLess::ct_lt(&b, &a)));
        assert!(!bool::from(ConstantTimeLess::ct_lt(&c, &a)));
        assert!(!bool::from(ConstantTimeLess::ct_lt(&c, &b)));
    }
}
