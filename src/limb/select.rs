//! Constant-time selection support.

use crate::{ConstChoice, CtSelect, Limb, word};

impl Limb {
    /// Return `b` if `c` is truthy, otherwise return `a`.
    #[inline]
    pub(crate) const fn select(a: Self, b: Self, c: ConstChoice) -> Self {
        Self(word::select(a.0, b.0, c))
    }

    /// Swap the values of `a` and `b` if `c` is truthy, otherwise do nothing.
    #[inline]
    pub(crate) const fn ct_conditional_swap(a: &mut Self, b: &mut Self, c: ConstChoice) {
        (*a, *b) = (
            Self(word::select(a.0, b.0, c)),
            Self(word::select(b.0, a.0, c)),
        )
    }
}

impl CtSelect for Limb {
    #[inline]
    fn ct_select(&self, other: &Self, choice: ConstChoice) -> Self {
        Self(self.0.ct_select(&other.0, choice))
    }
}

impl subtle::ConditionallySelectable for Limb {
    #[inline]
    fn conditional_select(a: &Self, b: &Self, choice: subtle::Choice) -> Self {
        a.ct_select(b, choice.into())
    }
}
