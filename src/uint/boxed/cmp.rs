//! [`BoxedUint`] comparisons.
//!
//! By default these are all constant-time and use the `subtle` crate.

pub(super) use core::cmp::{Ordering, max};

use super::BoxedUint;
use crate::{Choice, CtEq, CtGt, CtLt, CtSelect, Limb, Uint, word};

impl BoxedUint {
    /// Returns the Ordering between `self` and `rhs` in variable time.
    pub fn cmp_vartime(&self, rhs: &Self) -> Ordering {
        debug_assert_eq!(self.limbs.len(), rhs.limbs.len());
        let mut i = self.limbs.len() - 1;
        loop {
            // TODO: investigate if directly comparing limbs is faster than performing a
            // subtraction between limbs
            let (val, borrow) = self.limbs[i].borrowing_sub(rhs.limbs[i], Limb::ZERO);
            if val.0 != 0 {
                return if borrow.0 != 0 {
                    Ordering::Less
                } else {
                    Ordering::Greater
                };
            }
            if i == 0 {
                return Ordering::Equal;
            }
            i -= 1;
        }
    }

    /// Determine in variable time whether the `self` is zero.
    pub(crate) fn is_zero_vartime(&self) -> bool {
        !self.limbs.iter().any(|l| l.0 != 0)
    }
}

impl CtEq for BoxedUint {
    #[inline]
    fn ct_eq(&self, other: &Self) -> Choice {
        let limbs = max(self.nlimbs(), other.nlimbs());
        let mut ret = Choice::TRUE;

        for i in 0..limbs {
            let a = self.limbs.get(i).unwrap_or(&Limb::ZERO);
            let b = other.limbs.get(i).unwrap_or(&Limb::ZERO);
            ret &= a.ct_eq(b);
        }

        ret
    }
}

impl CtGt for BoxedUint {
    #[inline]
    fn ct_gt(&self, other: &Self) -> Choice {
        let (_, borrow) = other.borrowing_sub(self, Limb::ZERO);
        word::choice_from_mask(borrow.0)
    }
}

impl CtLt for BoxedUint {
    #[inline]
    fn ct_lt(&self, other: &Self) -> Choice {
        let (_, borrow) = self.borrowing_sub(other, Limb::ZERO);
        word::choice_from_mask(borrow.0)
    }
}

impl Eq for BoxedUint {}
impl PartialEq for BoxedUint {
    fn eq(&self, other: &Self) -> bool {
        self.ct_eq(other).into()
    }
}

impl<const LIMBS: usize> PartialEq<Uint<LIMBS>> for BoxedUint {
    fn eq(&self, other: &Uint<LIMBS>) -> bool {
        self.eq(&Self::from(other))
    }
}

impl Ord for BoxedUint {
    fn cmp(&self, other: &Self) -> Ordering {
        let mut ret = Ordering::Equal;
        ret.ct_assign(&Ordering::Greater, self.ct_gt(other));
        ret.ct_assign(&Ordering::Less, self.ct_lt(other));

        #[cfg(debug_assertions)]
        if ret == Ordering::Equal {
            debug_assert_eq!(self, other);
        }

        ret
    }
}

impl PartialOrd for BoxedUint {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<const LIMBS: usize> PartialOrd<Uint<LIMBS>> for BoxedUint {
    fn partial_cmp(&self, other: &Uint<LIMBS>) -> Option<Ordering> {
        self.partial_cmp(&Self::from(other))
    }
}

#[cfg(feature = "subtle")]
impl subtle::ConstantTimeEq for BoxedUint {
    #[inline]
    fn ct_eq(&self, other: &Self) -> subtle::Choice {
        CtEq::ct_eq(self, other).into()
    }
}

#[cfg(feature = "subtle")]
impl subtle::ConstantTimeGreater for BoxedUint {
    #[inline]
    fn ct_gt(&self, other: &Self) -> subtle::Choice {
        CtGt::ct_gt(self, other).into()
    }
}

#[cfg(feature = "subtle")]
impl subtle::ConstantTimeLess for BoxedUint {
    #[inline]
    fn ct_lt(&self, other: &Self) -> subtle::Choice {
        CtLt::ct_lt(self, other).into()
    }
}

#[cfg(test)]
mod tests {
    use super::BoxedUint;
    use crate::{CtEq, CtGt, CtLt};
    use core::cmp::Ordering;

    #[test]
    fn ct_eq() {
        let a = BoxedUint::zero();
        let b = BoxedUint::one();

        assert!(a.ct_eq(&a).to_bool());
        assert!(!a.ct_eq(&b).to_bool());
        assert!(!b.ct_eq(&a).to_bool());
        assert!(b.ct_eq(&b).to_bool());
    }

    #[test]
    fn ct_gt() {
        let a = BoxedUint::zero();
        let b = BoxedUint::one();
        let c = BoxedUint::max(64);

        assert!(b.ct_gt(&a).to_bool());
        assert!(c.ct_gt(&a).to_bool());
        assert!(c.ct_gt(&b).to_bool());

        assert!(!a.ct_gt(&a).to_bool());
        assert!(!b.ct_gt(&b).to_bool());
        assert!(!c.ct_gt(&c).to_bool());

        assert!(!a.ct_gt(&b).to_bool());
        assert!(!a.ct_gt(&c).to_bool());
        assert!(!b.ct_gt(&c).to_bool());
    }

    #[test]
    fn ct_lt() {
        let a = BoxedUint::zero();
        let b = BoxedUint::one();
        let c = BoxedUint::max(64);

        assert!(a.ct_lt(&b).to_bool());
        assert!(a.ct_lt(&c).to_bool());
        assert!(b.ct_lt(&c).to_bool());

        assert!(!a.ct_lt(&a).to_bool());
        assert!(!b.ct_lt(&b).to_bool());
        assert!(!c.ct_lt(&c).to_bool());

        assert!(!b.ct_lt(&a).to_bool());
        assert!(!c.ct_lt(&a).to_bool());
        assert!(!c.ct_lt(&b).to_bool());
    }

    #[test]
    fn cmp() {
        let a = BoxedUint::zero();
        let b = BoxedUint::one();
        let c = BoxedUint::max(64);

        assert_eq!(a.cmp(&b), Ordering::Less);
        assert_eq!(a.cmp(&c), Ordering::Less);
        assert_eq!(b.cmp(&c), Ordering::Less);

        assert_eq!(a.cmp(&a), Ordering::Equal);
        assert_eq!(b.cmp(&b), Ordering::Equal);
        assert_eq!(c.cmp(&c), Ordering::Equal);

        assert_eq!(b.cmp(&a), Ordering::Greater);
        assert_eq!(c.cmp(&a), Ordering::Greater);
        assert_eq!(c.cmp(&b), Ordering::Greater);
    }
}
