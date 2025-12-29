//! Constant-time selection support.

use super::BoxedUint;
use crate::{ConstChoice, CtSelect, Limb};

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

#[cfg(test)]
mod tests {
    use crate::{BoxedUint, ConstChoice, CtSelect};

    #[test]
    fn ct_select() {
        let a = BoxedUint::zero_with_precision(128);
        let b = BoxedUint::max(128);

        assert_eq!(a, BoxedUint::ct_select(&a, &b, ConstChoice::FALSE));
        assert_eq!(b, BoxedUint::ct_select(&a, &b, ConstChoice::TRUE));
    }
}
