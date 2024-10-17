//! [`Int`] negation-related operations.

use subtle::{Choice, CtOption};

use crate::{ConstChoice, ConstantTimeSelect, Int, Uint};

impl<const LIMBS: usize> Int<LIMBS> {
    /// Whether this [`Int`] is negative, as a `ConstChoice`.
    pub const fn is_negative(&self) -> ConstChoice {
        ConstChoice::from_word_msb(self.0.to_words()[LIMBS - 1])
    }

    /// Perform the two's complement "negate" operation on this [`Int`]:
    /// map `self` to `(self ^ 1111...1111) + 0000...0001`
    ///
    /// Returns
    /// - the result, as well as
    /// - whether the addition overflowed (indicating `self` is zero).
    ///
    /// Warning: this operation is unsafe; when `self == Self::MIN`, the negation fails.
    #[inline]
    pub(crate) const fn negate_unsafe(&self) -> (Self, ConstChoice) {
        let (val, carry) = self.0.wrapping_neg_with_carry();
        (Self(val), ConstChoice::from_word_lsb(carry))
    }

    /// Perform the [two's complement "negate" operation](Int::negate_unsafe) on this [`Int`]
    /// if `negate` is truthy.
    ///
    /// Returns
    /// - the result, as well as
    /// - whether the addition overflowed (indicating `self` is zero).
    ///
    /// Warning: this operation is unsafe; when `self == Self::MIN` and `negate` is truthy,
    /// the negation fails.
    #[inline]
    pub(crate) fn negate_if_unsafe(&self, negate: Choice) -> (Int<LIMBS>, Choice) {
        let (negated, is_zero) = self.negate_unsafe();
        (
            Self(Uint::ct_select(&self.0, &negated.0, negate)),
            is_zero.into(),
        )
    }

    /// Map this [`Int`] to `-self`.
    ///
    /// Yields `None` when `self == Self::MIN`, since an [`Int`] cannot represent the positive
    /// equivalent of that.
    pub fn neg(&self) -> CtOption<Self> {
        CtOption::new(self.negate_unsafe().0, !self.is_minimal())
    }
}

#[cfg(test)]
mod tests {
    use crate::{ConstChoice, I128};

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
