//! [`Int`] division operations.

use core::ops::Div;

use subtle::{Choice, CtOption};

use crate::{CheckedDiv, ConstChoice, ConstCtOption, Int, NonZero, Uint};

impl<const LIMBS: usize> Int<LIMBS> {
    #[inline]
    /// Base div_rem operation.
    /// Given `(a, b)`, computes the quotient and remainder of their absolute values. Furthermore,
    /// returns the signs of `a` and `b`.
    const fn div_rem_base(
        &self,
        rhs: &NonZero<Self>,
    ) -> (Uint<{ LIMBS }>, Uint<{ LIMBS }>, ConstChoice, ConstChoice) {
        // Step 1: split operands into signs and magnitudes.
        let (lhs_mag, lhs_sgn) = self.abs_sign();
        let (rhs_mag, rhs_sgn) = rhs.0.abs_sign();

        // Step 2. Divide magnitudes
        // safe to unwrap since rhs is NonZero.
        let (quotient, remainder) = lhs_mag.div_rem(&NonZero::<Uint<LIMBS>>::new_unwrap(rhs_mag));

        (quotient, remainder, lhs_sgn, rhs_sgn)
    }

    ///
    /// Example:
    /// ```
    /// use crypto_bigint::{I128, NonZero};
    /// let (quotient, remainder) = I128::from(8).checked_div_rem(&I128::from(3).to_nz().unwrap());
    /// assert_eq!(quotient.unwrap(), I128::from(2));
    /// assert_eq!(remainder.unwrap(), I128::from(2));
    ///
    /// let (quotient, remainder) = I128::from(-8).checked_div_rem(&I128::from(3).to_nz().unwrap());
    /// assert_eq!(quotient.unwrap(), I128::from(-2));
    /// assert_eq!(remainder.unwrap(), I128::from(-2));
    ///
    /// let (quotient, remainder) = I128::from(8).checked_div_rem(&I128::from(-3).to_nz().unwrap());
    /// assert_eq!(quotient.unwrap(), I128::from(-2));
    /// assert_eq!(remainder.unwrap(), I128::from(2));
    ///
    /// let (quotient, remainder) = I128::from(-8).checked_div_rem(&I128::from(-3).to_nz().unwrap());
    /// assert_eq!(quotient.unwrap(), I128::from(2));
    /// assert_eq!(remainder.unwrap(), I128::from(-2));
    /// ```
    pub const fn checked_div_rem(
        &self,
        rhs: &NonZero<Self>,
    ) -> (ConstCtOption<Self>, ConstCtOption<Self>) {
        let (quotient, remainder, lhs_sgn, rhs_sgn) = self.div_rem_base(rhs);
        let opposing_signs = lhs_sgn.ne(rhs_sgn);
        (
            Self::new_from_abs_sign(quotient, opposing_signs),
            Self::new_from_abs_sign(remainder, lhs_sgn),
        )
    }

    /// Perform checked division, returning a [`CtOption`] which `is_some` only if the rhs != 0.
    /// Note: this operation rounds towards zero, truncating any fractional part of the exact result.
    pub fn checked_div(&self, rhs: &Self) -> CtOption<Self> {
        NonZero::new(*rhs).and_then(|rhs| self.checked_div_rem(&rhs).0.into())
    }

    /// Perform checked division, returning a [`CtOption`] which `is_some` only if the rhs != 0.
    /// Note: this operation rounds down.
    ///
    /// Example:
    /// ```
    /// use crypto_bigint::I128;
    /// assert_eq!(
    ///     I128::from(8).checked_div_floor(&I128::from(3)).unwrap(),
    ///     I128::from(2)
    /// );
    /// assert_eq!(
    ///     I128::from(-8).checked_div_floor(&I128::from(3)).unwrap(),
    ///     I128::from(-3)
    /// );
    /// assert_eq!(
    ///     I128::from(8).checked_div_floor(&I128::from(-3)).unwrap(),
    ///     I128::from(-3)
    /// );
    /// assert_eq!(
    ///     I128::from(-8).checked_div_floor(&I128::from(-3)).unwrap(),
    ///     I128::from(2)
    /// )
    /// ```
    pub fn checked_div_floor(&self, rhs: &Self) -> CtOption<Self> {
        NonZero::new(*rhs).and_then(|rhs| {
            let (quotient, remainder, lhs_sgn, rhs_sgn) = self.div_rem_base(&rhs);

            // Increment the quotient when
            // - lhs and rhs have opposing signs, and
            // - there is a non-zero remainder.
            let opposing_signs = lhs_sgn.ne(rhs_sgn);
            let increment_quotient = remainder.is_nonzero().and(opposing_signs);
            let quotient_sub_one = quotient.wrapping_add(&Uint::ONE);
            let quotient = Uint::select(&quotient, &quotient_sub_one, increment_quotient);

            Self::new_from_abs_sign(quotient, opposing_signs).into()
        })
    }

    /// Perform checked division and mod, returning a [`CtOption`] which `is_some` only
    /// if the rhs != 0.
    /// Note: this operation rounds down.
    ///
    /// Example:
    /// ```
    /// use crypto_bigint::I128;
    /// assert_eq!(
    ///     I128::from(8).checked_div_mod_floor(&I128::from(3)).unwrap(),
    ///     (I128::from(2), I128::from(2))
    /// );
    /// assert_eq!(
    ///     I128::from(-8).checked_div_mod_floor(&I128::from(3)).unwrap(),
    ///     (I128::from(-3), I128::from(-1))
    /// );
    /// assert_eq!(
    ///     I128::from(8).checked_div_mod_floor(&I128::from(-3)).unwrap(),
    ///     (I128::from(-3), I128::from(-1))
    /// );
    /// assert_eq!(
    ///     I128::from(-8).checked_div_mod_floor(&I128::from(-3)).unwrap(),
    ///     (I128::from(2), I128::from(2))
    /// );
    /// ```
    pub fn checked_div_mod_floor(&self, rhs: &Self) -> CtOption<(Self, Self)> {
        let (lhs_mag, lhs_sgn) = self.abs_sign();
        let (rhs_mag, rhs_sgn) = rhs.abs_sign();
        let opposing_signs = lhs_sgn.xor(rhs_sgn);
        NonZero::new(rhs_mag).and_then(|rhs_mag| {
            let (quotient, remainder) = lhs_mag.div_rem(&rhs_mag);

            // Increase the quotient by one when lhs and rhs have opposing signs and there
            // is a non-zero remainder.
            let modify = remainder.is_nonzero().and(opposing_signs);
            let quotient_sub_one = quotient.wrapping_add(&Uint::ONE);
            let quotient = Uint::select(&quotient, &quotient_sub_one, modify);

            // Invert the remainder and add one to remainder when lhs and rhs have opposing signs
            // and the remainder is non-zero.
            let inv_remainder = rhs_mag.wrapping_sub(&remainder);
            let remainder = Uint::select(&remainder, &inv_remainder, modify);

            CtOption::from(Int::new_from_abs_sign(quotient, opposing_signs)).and_then(|quotient| {
                CtOption::from(Int::new_from_abs_sign(remainder, opposing_signs))
                    .and_then(|remainder| CtOption::new((quotient, remainder), Choice::from(1u8)))
            })
        })
    }
}

impl<const LIMBS: usize> CheckedDiv for Int<LIMBS> {
    fn checked_div(&self, rhs: &Int<LIMBS>) -> CtOption<Self> {
        self.checked_div(rhs).into()
    }
}

impl<const LIMBS: usize> Div<&NonZero<Int<LIMBS>>> for &Int<LIMBS> {
    type Output = CtOption<Int<LIMBS>>;

    fn div(self, rhs: &NonZero<Int<LIMBS>>) -> Self::Output {
        *self / *rhs
    }
}

impl<const LIMBS: usize> Div<&NonZero<Int<LIMBS>>> for Int<LIMBS> {
    type Output = CtOption<Int<LIMBS>>;

    fn div(self, rhs: &NonZero<Int<LIMBS>>) -> Self::Output {
        self / *rhs
    }
}

impl<const LIMBS: usize> Div<NonZero<Int<LIMBS>>> for &Int<LIMBS> {
    type Output = CtOption<Int<LIMBS>>;

    fn div(self, rhs: NonZero<Int<LIMBS>>) -> Self::Output {
        *self / rhs
    }
}

impl<const LIMBS: usize> Div<NonZero<Int<LIMBS>>> for Int<LIMBS> {
    type Output = CtOption<Int<LIMBS>>;

    fn div(self, rhs: NonZero<Int<LIMBS>>) -> Self::Output {
        self.checked_div(&rhs).into()
    }
}

#[cfg(test)]
mod tests {
    use crate::int::{Int, I128};

    #[test]
    fn test_checked_div() {
        let min_plus_one = Int {
            0: I128::MIN.0.wrapping_add(&I128::ONE.0),
        };

        // lhs = min

        let result = I128::MIN.checked_div(&I128::MIN);
        assert_eq!(result.unwrap(), I128::ONE);

        let result = I128::MIN.checked_div(&I128::MINUS_ONE);
        assert!(bool::from(result.is_none()));

        let result = I128::MIN.checked_div(&I128::ZERO);
        assert!(bool::from(result.is_none()));

        let result = I128::MIN.checked_div(&I128::ONE);
        assert_eq!(result.unwrap(), I128::MIN);

        let result = I128::MIN.checked_div(&I128::MAX);
        assert_eq!(result.unwrap(), I128::MINUS_ONE);

        // lhs = -1

        let result = I128::MINUS_ONE.checked_div(&I128::MIN);
        assert_eq!(result.unwrap(), I128::ZERO);

        let result = I128::MINUS_ONE.checked_div(&I128::MINUS_ONE);
        assert_eq!(result.unwrap(), I128::ONE);

        let result = I128::MINUS_ONE.checked_div(&I128::ZERO);
        assert!(bool::from(result.is_none()));

        let result = I128::MINUS_ONE.checked_div(&I128::ONE);
        assert_eq!(result.unwrap(), I128::MINUS_ONE);

        let result = I128::MINUS_ONE.checked_div(&I128::MAX);
        assert_eq!(result.unwrap(), I128::ZERO);

        // lhs = 0

        let result = I128::ZERO.checked_div(&I128::MIN);
        assert_eq!(result.unwrap(), I128::ZERO);

        let result = I128::ZERO.checked_div(&I128::MINUS_ONE);
        assert_eq!(result.unwrap(), I128::ZERO);

        let result = I128::ZERO.checked_div(&I128::ZERO);
        assert!(bool::from(result.is_none()));

        let result = I128::ZERO.checked_div(&I128::ONE);
        assert_eq!(result.unwrap(), I128::ZERO);

        let result = I128::ZERO.checked_div(&I128::MAX);
        assert_eq!(result.unwrap(), I128::ZERO);

        // lhs = 1

        let result = I128::ONE.checked_div(&I128::MIN);
        assert_eq!(result.unwrap(), I128::ZERO);

        let result = I128::ONE.checked_div(&I128::MINUS_ONE);
        assert_eq!(result.unwrap(), I128::MINUS_ONE);

        let result = I128::ONE.checked_div(&I128::ZERO);
        assert!(bool::from(result.is_none()));

        let result = I128::ONE.checked_div(&I128::ONE);
        assert_eq!(result.unwrap(), I128::ONE);

        let result = I128::ONE.checked_div(&I128::MAX);
        assert_eq!(result.unwrap(), I128::ZERO);

        // lhs = max

        let result = I128::MAX.checked_div(&I128::MIN);
        assert_eq!(result.unwrap(), I128::ZERO);

        let result = I128::MAX.checked_div(&I128::MINUS_ONE);
        assert_eq!(result.unwrap(), min_plus_one);

        let result = I128::MAX.checked_div(&I128::ZERO);
        assert!(bool::from(result.is_none()));

        let result = I128::MAX.checked_div(&I128::ONE);
        assert_eq!(result.unwrap(), I128::MAX);

        let result = I128::MAX.checked_div(&I128::MAX);
        assert_eq!(result.unwrap(), I128::ONE);
    }

    #[test]
    fn test_checked_div_floor() {
        assert_eq!(
            I128::from(8).checked_div_floor(&I128::from(3)).unwrap(),
            I128::from(2)
        );
        assert_eq!(
            I128::from(-8).checked_div_floor(&I128::from(3)).unwrap(),
            I128::from(-3)
        );
        assert_eq!(
            I128::from(8).checked_div_floor(&I128::from(-3)).unwrap(),
            I128::from(-3)
        );
        assert_eq!(
            I128::from(-8).checked_div_floor(&I128::from(-3)).unwrap(),
            I128::from(2)
        );
    }

    #[test]
    fn test_checked_div_mod_floor() {
        assert_eq!(
            I128::from(8).checked_div_mod_floor(&I128::from(3)).unwrap(),
            (I128::from(2), I128::from(2))
        );
        assert_eq!(
            I128::from(-8)
                .checked_div_mod_floor(&I128::from(3))
                .unwrap(),
            (I128::from(-3), I128::from(-1))
        );
        assert_eq!(
            I128::from(8)
                .checked_div_mod_floor(&I128::from(-3))
                .unwrap(),
            (I128::from(-3), I128::from(-1))
        );
        assert_eq!(
            I128::from(-8)
                .checked_div_mod_floor(&I128::from(-3))
                .unwrap(),
            (I128::from(2), I128::from(2))
        );
    }
}
