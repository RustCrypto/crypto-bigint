use crate::{ConstChoice, ConstCtOption, Int, Uint};

impl<const LIMBS: usize> Int<LIMBS> {
    /// Construct new [`Int`] from a sign and magnitude.
    /// Returns `None` when the magnitude does not fit in an [`Int<LIMBS>`].
    pub const fn new_from_abs_sign(
        abs: Uint<LIMBS>,
        is_negative: ConstChoice,
    ) -> ConstCtOption<Self> {
        let magnitude = Self(abs).wrapping_neg_if(is_negative);
        let fits = Uint::gt(&abs, &Int::MAX.0)
            .not()
            .or(is_negative.and(Uint::eq(&abs, &Int::MIN.0)));
        ConstCtOption::new(magnitude, fits)
    }

    /// Whether this [`Int`] is negative, as a `ConstChoice`.
    pub const fn is_negative(&self) -> ConstChoice {
        ConstChoice::from_word_msb(self.0.to_words()[LIMBS - 1])
    }

    /// Whether this [`Int`] is positive, as a `ConstChoice`.
    pub const fn is_positive(&self) -> ConstChoice {
        Int::is_negative(self).not().and(Int::is_nonzero(self))
    }

    /// The sign and magnitude of this [`Int`].
    pub const fn abs_sign(&self) -> (Uint<LIMBS>, ConstChoice) {
        let sign = self.is_negative();
        // Note: this negate_if is safe to use, since we are negating based on self.is_negative()
        let abs = self.wrapping_neg_if(sign);
        (abs.0, sign)
    }

    /// The magnitude of this [`Int`].
    pub const fn abs(&self) -> Uint<LIMBS> {
        self.abs_sign().0
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::I128;

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
    fn is_positive() {
        assert_eq!(I128::MIN.is_positive(), ConstChoice::FALSE);
        assert_eq!(I128::MINUS_ONE.is_positive(), ConstChoice::FALSE);
        assert_eq!(I128::ZERO.is_positive(), ConstChoice::FALSE);
        assert_eq!(I128::ONE.is_positive(), ConstChoice::TRUE);
        assert_eq!(I128::MAX.is_positive(), ConstChoice::TRUE);

        let random_negative = I128::from_be_hex("deadbeefcafebabedeadbeefcafebabe");
        assert_eq!(random_negative.is_positive(), ConstChoice::FALSE);

        let random_positive = I128::from_be_hex("0badc0dedeadc0decafebabedeadcafe");
        assert_eq!(random_positive.is_positive(), ConstChoice::TRUE);
    }
}
