//! Constant-time selection support.

use crate::{Choice, CtSelect, Int, Uint};

impl<const LIMBS: usize> Int<LIMBS> {
    /// Return `b` if `c` is truthy, otherwise return `a`.
    #[inline]
    pub(crate) const fn select(a: &Self, b: &Self, c: Choice) -> Self {
        Self(Uint::select(&a.0, &b.0, c))
    }
}

impl<const LIMBS: usize> CtSelect for Int<LIMBS> {
    #[inline]
    fn ct_select(&self, other: &Self, choice: Choice) -> Self {
        Self(self.0.ct_select(&other.0, choice))
    }
}

#[cfg(feature = "subtle")]
impl<const LIMBS: usize> subtle::ConditionallySelectable for Int<LIMBS> {
    #[inline]
    fn conditional_select(a: &Self, b: &Self, choice: subtle::Choice) -> Self {
        a.ct_select(b, choice.into())
    }
}

#[cfg(test)]
mod tests {
    use crate::{Choice, CtSelect, I128};

    #[test]
    fn ct_select() {
        let a = I128::from_be_hex("00002222444466668888AAAACCCCEEEE");
        let b = I128::from_be_hex("11113333555577779999BBBBDDDDFFFF");

        let select_0 = I128::ct_select(&a, &b, Choice::FALSE);
        assert_eq!(a, select_0);

        let select_1 = I128::ct_select(&a, &b, Choice::TRUE);
        assert_eq!(b, select_1);
    }
}
