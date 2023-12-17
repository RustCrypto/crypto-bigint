//! [`BoxedUint`] negation operations.

use crate::{BoxedUint, ConstantTimeSelect, Limb, WideWord, Word, WrappingNeg};
use subtle::Choice;

impl BoxedUint {
    /// Negates based on `choice` by wrapping the integer.
    pub(crate) fn conditional_wrapping_neg(&self, choice: Choice) -> BoxedUint {
        Self::ct_select(self, &self.wrapping_neg(), choice)
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

impl WrappingNeg for BoxedUint {
    fn wrapping_neg(&self) -> Self {
        self.wrapping_neg()
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
