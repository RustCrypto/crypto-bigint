use crate::{ConstChoice, Limb, Uint, WideWord, Word, WrappingNeg};

impl<const LIMBS: usize> Uint<LIMBS> {
    /// Perform wrapping negation.
    pub const fn wrapping_neg(&self) -> Self {
        self.carrying_neg().0
    }

    /// Perform negation; additionally return the carry.
    /// Note: the carry equals `Word::ZERO` when `self == Self::ZERO`, and `Word::MAX` otherwise.
    pub const fn carrying_neg(&self) -> (Self, Word) {
        let mut ret = [Limb::ZERO; LIMBS];
        let mut carry = 1;
        let mut i = 0;
        while i < LIMBS {
            let r = (!self.limbs[i].0 as WideWord) + carry;
            ret[i] = Limb(r as Word);
            carry = r >> Limb::BITS;
            i += 1;
        }
        (Uint::new(ret), carry.wrapping_add(!0) as Word)
    }

    /// Perform negation, if `negate` is truthy.
    pub const fn wrapping_neg_if(&self, negate: ConstChoice) -> Self {
        Uint::select(self, &self.wrapping_neg(), negate)
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
    use num_traits::ConstZero;

    use crate::{ConstChoice, Word, U256};

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

    #[test]
    fn carrying_neg() {
        assert_eq!(U256::ZERO.carrying_neg(), (U256::ZERO, Word::ZERO));
        assert_eq!(U256::ONE.carrying_neg(), (U256::MAX, Word::MAX));
        assert_eq!(U256::MAX.carrying_neg(), (U256::ONE, Word::MAX));
    }

    #[test]
    fn wrapping_neg_if() {
        let negate = ConstChoice::TRUE;
        assert_eq!(U256::ZERO.wrapping_neg_if(negate), U256::ZERO);
        assert_eq!(U256::ONE.wrapping_neg_if(negate), U256::MAX);
        assert_eq!(U256::MAX.wrapping_neg_if(negate), U256::ONE);

        let do_not_negate = ConstChoice::FALSE;
        assert_eq!(U256::ZERO.wrapping_neg_if(do_not_negate), U256::ZERO);
        assert_eq!(U256::ONE.wrapping_neg_if(do_not_negate), U256::ONE);
        assert_eq!(U256::MAX.wrapping_neg_if(do_not_negate), U256::MAX);
    }
}
