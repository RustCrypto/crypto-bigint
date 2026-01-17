//! Constant-time support: impls of `Ct*` traits.

use super::BoxedUint;
use crate::{Choice, CtEq, CtGt, CtLt, CtNeg, CtSelect, Limb, word};
use core::cmp::max;

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

impl CtNeg for BoxedUint {
    fn ct_neg(&self, choice: Choice) -> Self {
        let self_neg = self.wrapping_neg();
        self.ct_select(&self_neg, choice)
    }

    fn ct_neg_assign(&mut self, choice: Choice) {
        let self_neg = self.wrapping_neg();
        self.ct_assign(&self_neg, choice)
    }
}

impl CtSelect for BoxedUint {
    #[inline]
    fn ct_select(&self, other: &Self, choice: Choice) -> Self {
        debug_assert_eq!(self.bits_precision(), other.bits_precision());
        let mut limbs = vec![Limb::ZERO; self.nlimbs()].into_boxed_slice();

        for i in 0..self.nlimbs() {
            limbs[i] = self.limbs[i].ct_select(&other.limbs[i], choice);
        }

        Self { limbs }
    }

    #[inline]
    fn ct_assign(&mut self, other: &Self, choice: Choice) {
        debug_assert_eq!(self.bits_precision(), other.bits_precision());

        for i in 0..self.nlimbs() {
            self.limbs[i].ct_assign(&other.limbs[i], choice);
        }
    }

    #[inline]
    fn ct_swap(&mut self, other: &mut Self, choice: Choice) {
        debug_assert_eq!(self.bits_precision(), other.bits_precision());

        for i in 0..self.nlimbs() {
            self.limbs[i].ct_swap(&mut other.limbs[i], choice);
        }
    }
}

#[cfg(feature = "subtle")]
impl subtle::ConditionallyNegatable for BoxedUint {
    #[inline]
    fn conditional_negate(&mut self, choice: subtle::Choice) {
        self.ct_neg_assign(choice.into())
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
    use crate::{BoxedUint, Choice, CtEq, CtGt, CtLt, CtSelect};

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
    fn ct_select() {
        let a = BoxedUint::zero_with_precision(128);
        let b = BoxedUint::max(128);

        assert_eq!(a, BoxedUint::ct_select(&a, &b, Choice::FALSE));
        assert_eq!(b, BoxedUint::ct_select(&a, &b, Choice::TRUE));
    }
}
