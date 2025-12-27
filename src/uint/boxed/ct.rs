//! Constant-time helper functions.

use super::BoxedUint;
use crate::{ConstChoice, CtSelect, Limb};
use subtle::{Choice, ConditionallyNegatable};

impl CtSelect for BoxedUint {
    #[inline]
    fn ct_select(&self, other: &Self, choice: ConstChoice) -> Self {
        debug_assert_eq!(self.bits_precision(), other.bits_precision());
        let mut limbs = vec![Limb::ZERO; self.nlimbs()].into_boxed_slice();

        for i in 0..self.nlimbs() {
            limbs[i] = self.limbs[i].ct_select(&other.limbs[i], choice);
        }

        Self { limbs }
    }

    #[inline]
    fn ct_assign(&mut self, other: &Self, choice: ConstChoice) {
        debug_assert_eq!(self.bits_precision(), other.bits_precision());

        for i in 0..self.nlimbs() {
            self.limbs[i].ct_assign(&other.limbs[i], choice);
        }
    }

    #[inline]
    fn ct_swap(&mut self, other: &mut Self, choice: ConstChoice) {
        debug_assert_eq!(self.bits_precision(), other.bits_precision());

        for i in 0..self.nlimbs() {
            self.limbs[i].ct_swap(&mut other.limbs[i], choice);
        }
    }
}

impl ConditionallyNegatable for BoxedUint {
    #[inline]
    fn conditional_negate(&mut self, choice: Choice) {
        let self_neg = self.wrapping_neg();
        self.ct_assign(&self_neg, choice.into())
    }
}

#[cfg(test)]
mod tests {
    use crate::{BoxedUint, ConstChoice, CtSelect};
    use subtle::ConditionallyNegatable;

    #[test]
    fn conditional_select() {
        let a = BoxedUint::zero_with_precision(128);
        let b = BoxedUint::max(128);

        assert_eq!(a, BoxedUint::ct_select(&a, &b, ConstChoice::FALSE));
        assert_eq!(b, BoxedUint::ct_select(&a, &b, ConstChoice::TRUE));
    }

    #[test]
    fn conditional_negate() {
        let mut a = BoxedUint::from(123u64);
        let control = a.clone();

        a.conditional_negate(ConstChoice::FALSE.into());
        assert_eq!(a, control);

        a.conditional_negate(ConstChoice::TRUE.into());
        assert_ne!(a, control);
        assert_eq!(a, control.wrapping_neg());
    }
}
