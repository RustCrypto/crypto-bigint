//! Constant-time helper functions.

use super::BoxedUint;
use crate::{ConstantTimeSelect, Limb};
use subtle::{Choice, ConditionallySelectable};

/// NOTE: can't impl `subtle`'s [`ConditionallySelectable`] trait due to its `Copy` bound
impl ConstantTimeSelect for BoxedUint {
    #[inline]
    fn ct_select(a: &Self, b: &Self, choice: Choice) -> Self {
        debug_assert_eq!(a.bits_precision(), b.bits_precision());
        let mut limbs = vec![Limb::ZERO; a.nlimbs()].into_boxed_slice();

        for i in 0..a.nlimbs() {
            limbs[i] = Limb::conditional_select(&a.limbs[i], &b.limbs[i], choice);
        }

        Self { limbs }
    }

    #[inline]
    fn ct_assign(&mut self, other: &Self, choice: Choice) {
        debug_assert_eq!(self.bits_precision(), other.bits_precision());

        for i in 0..self.nlimbs() {
            self.limbs[i].conditional_assign(&other.limbs[i], choice);
        }
    }

    #[inline]
    fn ct_swap(a: &mut Self, b: &mut Self, choice: Choice) {
        debug_assert_eq!(a.bits_precision(), b.bits_precision());

        for i in 0..a.nlimbs() {
            Limb::conditional_swap(&mut a.limbs[i], &mut b.limbs[i], choice);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::BoxedUint;
    use crate::ConstantTimeSelect;
    use subtle::Choice;

    #[test]
    fn conditional_select() {
        let a = BoxedUint::zero_with_precision(128);
        let b = BoxedUint::max(128);

        assert_eq!(a, BoxedUint::ct_select(&a, &b, Choice::from(0)));
        assert_eq!(b, BoxedUint::ct_select(&a, &b, Choice::from(1)));
    }
}
