//! Limb comparisons

use crate::{ConstChoice, Limb};
use core::cmp::Ordering;
use subtle::{
    Choice, ConditionallySelectable, ConstantTimeEq, ConstantTimeGreater, ConstantTimeLess,
};

impl Limb {
    /// Is this limb an odd number?
    #[inline]
    pub fn is_odd(&self) -> Choice {
        Choice::from(self.0 as u8 & 1)
    }

    /// Perform a comparison of the inner value in variable-time.
    ///
    /// Note that the [`PartialOrd`] and [`Ord`] impls wrap constant-time
    /// comparisons using the `subtle` crate.
    pub fn cmp_vartime(&self, other: &Self) -> Ordering {
        self.0.cmp(&other.0)
    }

    /// Performs an equality check in variable-time.
    pub const fn eq_vartime(&self, other: &Self) -> bool {
        self.0 == other.0
    }

    /// Return `b` if `c` is truthy, otherwise return `a`.
    #[inline]
    pub(crate) const fn select(a: Self, b: Self, c: ConstChoice) -> Self {
        Self(c.select_word(a.0, b.0))
    }

    /// Returns the truthy value if `self != 0` and the falsy value otherwise.
    #[inline]
    pub(crate) const fn is_nonzero(&self) -> ConstChoice {
        ConstChoice::from_word_nonzero(self.0)
    }
}

impl ConstantTimeEq for Limb {
    #[inline]
    fn ct_eq(&self, other: &Self) -> Choice {
        self.0.ct_eq(&other.0)
    }

    #[inline]
    fn ct_ne(&self, other: &Self) -> Choice {
        self.0.ct_ne(&other.0)
    }
}

impl ConstantTimeGreater for Limb {
    #[inline]
    fn ct_gt(&self, other: &Self) -> Choice {
        ConstChoice::from_word_gt(self.0, other.0).into()
    }
}

impl ConstantTimeLess for Limb {
    #[inline]
    fn ct_lt(&self, other: &Self) -> Choice {
        ConstChoice::from_word_lt(self.0, other.0).into()
    }
}

impl Eq for Limb {}

impl Ord for Limb {
    fn cmp(&self, other: &Self) -> Ordering {
        let mut ret = Ordering::Less;
        ret.conditional_assign(&Ordering::Equal, self.ct_eq(other));
        ret.conditional_assign(&Ordering::Greater, self.ct_gt(other));
        debug_assert_eq!(ret == Ordering::Less, bool::from(self.ct_lt(other)));
        ret
    }
}

impl PartialOrd for Limb {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl PartialEq for Limb {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.ct_eq(other).into()
    }
}

#[cfg(test)]
mod tests {
    use crate::{Limb, Zero};
    use core::cmp::Ordering;
    use subtle::{ConstantTimeEq, ConstantTimeGreater, ConstantTimeLess};

    #[test]
    fn is_zero() {
        assert!(bool::from(Limb::ZERO.is_zero()));
        assert!(!bool::from(Limb::ONE.is_zero()));
        assert!(!bool::from(Limb::MAX.is_zero()));
    }

    #[test]
    fn is_odd() {
        assert!(!bool::from(Limb::ZERO.is_odd()));
        assert!(bool::from(Limb::ONE.is_odd()));
        assert!(bool::from(Limb::MAX.is_odd()));
    }

    #[test]
    fn ct_eq() {
        let a = Limb::ZERO;
        let b = Limb::MAX;

        assert!(bool::from(a.ct_eq(&a)));
        assert!(!bool::from(a.ct_eq(&b)));
        assert!(!bool::from(b.ct_eq(&a)));
        assert!(bool::from(b.ct_eq(&b)));
    }

    #[test]
    fn ct_gt() {
        let a = Limb::ZERO;
        let b = Limb::ONE;
        let c = Limb::MAX;

        assert!(bool::from(b.ct_gt(&a)));
        assert!(bool::from(c.ct_gt(&a)));
        assert!(bool::from(c.ct_gt(&b)));

        assert!(!bool::from(a.ct_gt(&a)));
        assert!(!bool::from(b.ct_gt(&b)));
        assert!(!bool::from(c.ct_gt(&c)));

        assert!(!bool::from(a.ct_gt(&b)));
        assert!(!bool::from(a.ct_gt(&c)));
        assert!(!bool::from(b.ct_gt(&c)));
    }

    #[test]
    fn ct_lt() {
        let a = Limb::ZERO;
        let b = Limb::ONE;
        let c = Limb::MAX;

        assert!(bool::from(a.ct_lt(&b)));
        assert!(bool::from(a.ct_lt(&c)));
        assert!(bool::from(b.ct_lt(&c)));

        assert!(!bool::from(a.ct_lt(&a)));
        assert!(!bool::from(b.ct_lt(&b)));
        assert!(!bool::from(c.ct_lt(&c)));

        assert!(!bool::from(b.ct_lt(&a)));
        assert!(!bool::from(c.ct_lt(&a)));
        assert!(!bool::from(c.ct_lt(&b)));
    }

    #[test]
    fn cmp() {
        assert_eq!(Limb::ZERO.cmp(&Limb::ONE), Ordering::Less);
        assert_eq!(Limb::ONE.cmp(&Limb::ONE), Ordering::Equal);
        assert_eq!(Limb::MAX.cmp(&Limb::ONE), Ordering::Greater);
    }
}
