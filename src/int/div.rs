//! [`Int`] division operations.

use core::ops::Div;

use subtle::{Choice, CtOption};

use crate::{CheckedDiv, ConstChoice, Int, NonZero, Uint};

impl<const LIMBS: usize> Int<LIMBS> {
    #[inline]
    /// Base checked_div_mod operation.
    /// Given `(a, b)` computes the quotient and remainder of the absolute
    /// Note: this operation rounds towards zero, truncating any fractional part of the exact result.
    fn checked_div_mod(
        &self,
        rhs: &NonZero<Self>,
    ) -> (Uint<{ LIMBS }>, Uint<{ LIMBS }>, ConstChoice) {
        // Step 1: split operands into signs, magnitudes and whether they are zero.
        let (lhs_sgn, lhs_mag) = self.sign_and_magnitude();
        let (rhs_sgn, rhs_mag) = rhs.sign_and_magnitude();

        // Step 2. Determine if the result should be negated.
        // This should be done if and only if lhs and rhs have opposing signs.
        // Note: if the lhs is zero, the resulting magnitude will also be zero. Negating zero,
        // however, still yields zero, so having a truthy `negate_result` in that scenario is OK.
        let opposing_signs = lhs_sgn.xor(rhs_sgn);

        // Step 3. Construct result
        // safe to unwrap since rhs is NonZero.
        let (quotient, remainder) = lhs_mag.div_rem(&NonZero::new(rhs_mag).unwrap());

        (quotient, remainder, opposing_signs)
    }

    /// Perform checked division, returning a [`CtOption`] which `is_some` only if the rhs != 0.
    /// Note: this operation rounds towards zero, truncating any fractional part of the exact result.
    pub fn checked_div(&self, rhs: &Self) -> CtOption<Self> {
        NonZero::new(*rhs).and_then(|rhs| {
            let (quotient, _, opposing_signs) = self.checked_div_mod(&rhs);
            Self::new_from_sign_and_magnitude(opposing_signs, quotient).into()
        })
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
            let (quotient, remainder, opposing_signs) = self.checked_div_mod(&rhs);

            // Increase the quotient by one when lhs and rhs have opposing signs and there
            // is a non-zero remainder.
            let increment_quotient = remainder.is_nonzero().and(opposing_signs);
            let quotient_sub_one = quotient.wrapping_add(&Uint::ONE);
            let quotient = Uint::select(&quotient, &quotient_sub_one, increment_quotient);

            Self::new_from_sign_and_magnitude(opposing_signs, quotient).into()
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
        let (lhs_sgn, lhs_mag) = self.sign_and_magnitude();
        let (rhs_sgn, rhs_mag) = rhs.sign_and_magnitude();
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

            CtOption::from(Int::new_from_sign_and_magnitude(opposing_signs, quotient)).and_then(
                |quotient| {
                    CtOption::from(Int::new_from_sign_and_magnitude(opposing_signs, remainder))
                        .and_then(|remainder| {
                            CtOption::new((quotient, remainder), Choice::from(1u8))
                        })
                },
            )
        })
    }
}

impl<const LIMBS: usize> CheckedDiv for Int<LIMBS> {
    fn checked_div(&self, rhs: &Int<LIMBS>) -> CtOption<Self> {
        self.checked_div(rhs)
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
        self.checked_div(&rhs)
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
