//! [`BoxedUint`] negation operations.

use crate::{BoxedUint, Limb, WideWord, Word, Wrapping};
use core::ops::Neg;
use subtle::Choice;

impl Neg for Wrapping<BoxedUint> {
    type Output = Self;

    fn neg(self) -> Self::Output {
        Self(self.0.wrapping_neg())
    }
}

impl BoxedUint {
    /// Negates based on `choice` by wrapping the integer.
    pub(crate) fn conditional_wrapping_neg(&self, choice: Choice) -> BoxedUint {
        Self::conditional_select(self, &self.wrapping_neg(), choice)
    }

    /// Perform wrapping negation.
    pub fn wrapping_neg(&self) -> Self {
        let mut ret = vec![Limb::ZERO; self.nlimbs()];
        let mut carry = 1;

        for i in 0..self.nlimbs() {
            let r = (!self.limbs[i].0 as WideWord) + carry;
            ret[i] = Limb(r as Word);
            carry = r >> Limb::BITS;
        }

        ret.into()
    }
}

#[cfg(test)]
mod tests {
    use crate::BoxedUint;

    #[test]
    fn wrapping_neg() {
        assert_eq!(BoxedUint::zero().wrapping_neg(), BoxedUint::zero());
        assert_eq!(BoxedUint::max(64).wrapping_neg(), BoxedUint::one());
        // assert_eq!(
        //     BoxedUint::from(13u64).wrapping_neg(),
        //     BoxedUint::from(13u64).not().saturating_add(&BoxedUint::one())
        // );
        // assert_eq!(
        //     BoxedUint::from(42u64).wrapping_neg(),
        //     BoxedUint::from(42u64).saturating_sub(&BoxedUint::one()).not()
        // );
    }
}
