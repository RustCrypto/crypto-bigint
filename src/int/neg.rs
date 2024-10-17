//! [`Int`] negation-related operations.

use subtle::CtOption;

use crate::{ConstChoice, Int, Word};

impl<const LIMBS: usize> Int<LIMBS> {
    /// Whether this [`Int`] is negative, as a `ConstChoice`.
    pub const fn is_negative(&self) -> ConstChoice {
        ConstChoice::from_word_msb(self.0.to_words()[LIMBS - 1])
    }

    /// Perform the two's complement "negate" operation on this [`Int`]:
    /// map `self` to `(self ^ 1111...1111) + 0000...0001` and return the carry.
    ///
    /// Note: a non-zero carry indicates `self == Self::ZERO`.
    ///
    /// Warning: this operation is unsafe to use as negation; the negation is incorrect when
    /// `self == Self::MIN`.
    #[inline]
    pub(crate) const fn negc(&self) -> (Self, Word) {
        let (val, carry) = self.0.negc();
        (Self(val), carry)
    }

    /// Wrapping negate this [`Int`] if `negate` is truthy; otherwise do nothing.
    ///
    /// Warning: this operation is unsafe to use as negation; the result is incorrect when
    /// `self == Self::MIN` and `negate` is truthy.
    #[inline]
    pub(crate) const fn wrapping_neg_if(&self, negate: ConstChoice) -> Int<LIMBS> {
        Self(self.0.wrapping_neg_if(negate))
    }

    /// Map this [`Int`] to `-self`.
    ///
    /// Yields `None` when `self == Self::MIN`, since an [`Int`] cannot represent the positive
    /// equivalent of that.
    pub fn neg(&self) -> CtOption<Self> {
        CtOption::new(self.negc().0, !self.is_minimal())
    }
}

#[cfg(test)]
mod tests {
    use num_traits::{ConstOne, ConstZero};

    use crate::{ConstChoice, Word, I128};

    #[test]
    fn is_negative() {
        assert_eq!(I128::MIN.is_negative(), ConstChoice::TRUE);
        assert_eq!(I128::MINUS_ONE.is_negative(), ConstChoice::TRUE);
        assert_eq!(I128::ZERO.is_negative(), ConstChoice::FALSE);
        assert_eq!(I128::ONE.is_negative(), ConstChoice::FALSE);
        assert_eq!(I128::MAX.is_negative(), ConstChoice::FALSE);

        let random_negative = I128::from_be_hex("91113333555577779999BBBBDDDDFFFF");
        assert_eq!(random_negative.is_negative(), ConstChoice::TRUE);

        let random_positive = I128::from_be_hex("71113333555577779999BBBBDDDDFFFF");
        assert_eq!(random_positive.is_negative(), ConstChoice::FALSE);
    }

    #[test]
    fn negate_unsafe() {
        let min_plus_one = I128 {
            0: I128::MIN.0.wrapping_add(&I128::ONE.0),
        };

        let (res, carry) = I128::MIN.negc();
        assert_eq!(carry, Word::ZERO);
        assert_eq!(res, I128::MIN);

        let (res, carry) = I128::MINUS_ONE.negc();
        assert_eq!(carry, Word::ZERO);
        assert_eq!(res, I128::ONE);

        let (res, carry) = I128::ZERO.negc();
        assert_eq!(carry, Word::ONE);
        assert_eq!(res, I128::ZERO);

        let (res, carry) = I128::ONE.negc();
        assert_eq!(carry, Word::ZERO);
        assert_eq!(res, I128::MINUS_ONE);

        let (res, carry) = I128::MAX.negc();
        assert_eq!(carry, Word::ZERO);
        assert_eq!(res, min_plus_one);
    }

    #[test]
    fn negate_if_unsafe() {
        let min_plus_one = I128 {
            0: I128::MIN.0.wrapping_add(&I128::ONE.0),
        };

        let do_negate = ConstChoice::TRUE.into();
        assert_eq!(I128::MIN.wrapping_neg_if(do_negate), I128::MIN);
        assert_eq!(I128::MINUS_ONE.wrapping_neg_if(do_negate), I128::ONE);
        assert_eq!(I128::ZERO.wrapping_neg_if(do_negate), I128::ZERO);
        assert_eq!(I128::ONE.wrapping_neg_if(do_negate), I128::MINUS_ONE);
        assert_eq!(I128::MAX.wrapping_neg_if(do_negate), min_plus_one);

        let do_not_negate = ConstChoice::FALSE.into();
        assert_eq!(I128::MIN.wrapping_neg_if(do_not_negate), I128::MIN);
        assert_eq!(
            I128::MINUS_ONE.wrapping_neg_if(do_not_negate),
            I128::MINUS_ONE
        );
        assert_eq!(I128::ZERO.wrapping_neg_if(do_not_negate), I128::ZERO);
        assert_eq!(I128::ONE.wrapping_neg_if(do_not_negate), I128::ONE);
        assert_eq!(I128::MAX.wrapping_neg_if(do_not_negate), I128::MAX);
    }

    #[test]
    fn neg() {
        assert_eq!(I128::MIN.neg().is_none().unwrap_u8(), 1u8);
        assert_eq!(I128::MINUS_ONE.neg().unwrap(), I128::ONE);
        assert_eq!(I128::ZERO.neg().unwrap(), I128::ZERO);
        assert_eq!(I128::ONE.neg().unwrap(), I128::MINUS_ONE);
        assert_eq!(
            I128::MAX.neg().unwrap(),
            I128::from_be_hex("80000000000000000000000000000001")
        );

        let negative = I128::from_be_hex("91113333555577779999BBBBDDDDFFFF");
        let positive = I128::from_be_hex("6EEECCCCAAAA88886666444422220001");
        assert_eq!(negative.neg().unwrap(), positive);
        assert_eq!(positive.neg().unwrap(), negative);
        assert_eq!(positive.neg().unwrap().neg().unwrap(), positive);
    }
}
