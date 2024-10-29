//! [`Int`] negation-related operations.

use crate::{ConstChoice, ConstCtOption, Int, Word};

impl<const LIMBS: usize> Int<LIMBS> {
    /// Perform the two's complement "negate" operation on this [`Int`]:
    /// map `self` to `(self ^ 1111...1111) + 0000...0001` and return the carry.
    ///
    /// Note: a non-zero carry indicates `self == Self::ZERO`.
    ///
    /// Warning: this operation is unsafe to use as negation; the negation is incorrect when
    /// `self == Self::MIN`.
    #[inline]
    pub(crate) const fn carrying_neg(&self) -> (Self, Word) {
        let (val, carry) = self.0.carrying_neg();
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
    pub const fn neg(&self) -> ConstCtOption<Self> {
        ConstCtOption::new(self.carrying_neg().0, self.is_min().not())
    }
}

#[cfg(test)]
mod tests {
    use num_traits::ConstZero;

    use crate::{ConstChoice, Word, I128};

    #[test]
    fn carrying_neg() {
        let min_plus_one = I128 {
            0: I128::MIN.0.wrapping_add(&I128::ONE.0),
        };

        let (res, carry) = I128::MIN.carrying_neg();
        assert_eq!(carry, Word::MAX);
        assert_eq!(res, I128::MIN);

        let (res, carry) = I128::MINUS_ONE.carrying_neg();
        assert_eq!(carry, Word::MAX);
        assert_eq!(res, I128::ONE);

        let (res, carry) = I128::ZERO.carrying_neg();
        assert_eq!(carry, Word::ZERO);
        assert_eq!(res, I128::ZERO);

        let (res, carry) = I128::ONE.carrying_neg();
        assert_eq!(carry, Word::MAX);
        assert_eq!(res, I128::MINUS_ONE);

        let (res, carry) = I128::MAX.carrying_neg();
        assert_eq!(carry, Word::MAX);
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
        assert_eq!(I128::MIN.neg().is_none(), ConstChoice::TRUE);
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
