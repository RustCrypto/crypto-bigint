//! Constant-time selection support.

use crate::{Choice, CtSelect, Limb, Uint};

impl<const LIMBS: usize> Uint<LIMBS> {
    /// Return `b` if `c` is truthy, otherwise return `a`.
    #[inline]
    pub(crate) const fn select(a: &Self, b: &Self, c: Choice) -> Self {
        let mut limbs = [Limb::ZERO; LIMBS];

        let mut i = 0;
        while i < LIMBS {
            limbs[i] = Limb::select(a.limbs[i], b.limbs[i], c);
            i += 1;
        }

        Uint { limbs }
    }

    /// Swap `a` and `b` if `c` is truthy, otherwise, do nothing.
    #[inline]
    pub(crate) const fn conditional_swap(a: &mut Self, b: &mut Self, c: Choice) {
        let mut i = 0;
        let a = a.as_mut_limbs();
        let b = b.as_mut_limbs();
        while i < LIMBS {
            Limb::ct_conditional_swap(&mut a[i], &mut b[i], c);
            i += 1;
        }
    }

    /// Swap `a` and `b`
    #[inline]
    pub(crate) const fn swap(a: &mut Self, b: &mut Self) {
        Self::conditional_swap(a, b, Choice::TRUE)
    }
}

impl<const LIMBS: usize> CtSelect for Uint<LIMBS> {
    #[inline]
    fn ct_select(&self, other: &Self, choice: Choice) -> Self {
        Self {
            limbs: self.limbs.ct_select(&other.limbs, choice),
        }
    }
}

#[cfg(feature = "subtle")]
impl<const LIMBS: usize> subtle::ConditionallySelectable for Uint<LIMBS> {
    #[inline]
    fn conditional_select(a: &Self, b: &Self, choice: subtle::Choice) -> Self {
        a.ct_select(b, choice.into())
    }
}

#[cfg(test)]
mod tests {
    use crate::{Choice, CtSelect, U128};

    #[test]
    fn ct_select() {
        let a = U128::from_be_hex("00002222444466668888AAAACCCCEEEE");
        let b = U128::from_be_hex("11113333555577779999BBBBDDDDFFFF");

        let select_0 = U128::ct_select(&a, &b, Choice::FALSE);
        assert_eq!(a, select_0);

        let select_1 = U128::ct_select(&a, &b, Choice::TRUE);
        assert_eq!(b, select_1);
    }
}
