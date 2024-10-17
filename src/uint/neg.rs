use num_traits::ConstOne;

use crate::{ConstChoice, Limb, Uint, WideWord, Word, WrappingNeg};

impl<const LIMBS: usize> Uint<LIMBS> {
    /// Perform wrapping negation.
    pub const fn wrapping_neg(&self) -> Self {
        self.negc().0
    }

    /// Perform negation; additionally return the carry.
    pub const fn negc(&self) -> (Self, Word) {
        let mut ret = [Limb::ZERO; LIMBS];
        let mut carry = 1;
        let mut i = 0;
        while i < LIMBS {
            let r = (!self.limbs[i].0 as WideWord) + carry;
            ret[i] = Limb(r as Word);
            carry = r >> Limb::BITS;
            i += 1;
        }
        (Uint::new(ret), carry as Word)
    }

    /// Perform negation, if `negate` is truthy.
    pub const fn wrapping_neg_if(&self, negate: ConstChoice) -> Self {
        let mut ret = [Limb::ZERO; LIMBS];
        let mut i = 0;
        let mask = negate.as_word_mask() as WideWord;
        let mut carry = mask & WideWord::ONE;
        while i < LIMBS {
            let r = ((self.limbs[i].0 as WideWord) ^ mask) + carry;
            ret[i] = Limb(r as Word);
            carry = r >> Limb::BITS;
            i += 1;
        }
        Uint::new(ret)
    }
}

impl<const LIMBS: usize> WrappingNeg for Uint<LIMBS> {
    #[inline]
    fn wrapping_neg(&self) -> Self {
        self.wrapping_neg()
    }
}

#[cfg(test)]
mod tests {
    use crate::U256;

    #[test]
    fn wrapping_neg() {
        assert_eq!(U256::ZERO.wrapping_neg(), U256::ZERO);
        assert_eq!(U256::MAX.wrapping_neg(), U256::ONE);
        assert_eq!(
            U256::from_u64(13).wrapping_neg(),
            U256::from_u64(13).not().saturating_add(&U256::ONE)
        );
        assert_eq!(
            U256::from_u64(42).wrapping_neg(),
            U256::from_u64(42).saturating_sub(&U256::ONE).not()
        );
    }
}
