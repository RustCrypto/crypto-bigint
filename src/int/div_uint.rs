//! [`Int`] divide by [`Uint`] operations.
use core::ops::Div;

use subtle::{Choice, CtOption};

use crate::{ConstChoice, Int, NonZero, Uint};

/// Operations related to dividing an [`Int`] by a [`Uint`].
impl<const LIMBS: usize> Int<LIMBS> {
    #[inline]
    /// Base div_rem operation on dividing an [`Int`] by a [`Uint`].
    /// Computes the quotient and remainder of `self / rhs`.
    /// Furthermore, returns the sign of `self`.
    const fn div_rem_base_uint(
        &self,
        rhs: &NonZero<Uint<LIMBS>>,
    ) -> (Uint<{ LIMBS }>, Uint<{ LIMBS }>, ConstChoice) {
        // Step 1: split operand into sign and magnitude.
        let (lhs_mag, lhs_sgn) = self.abs_sign();

        // Step 2. Divide magnitudes
        // safe to unwrap since rhs is NonZero.
        let (quotient, remainder) = lhs_mag.div_rem(&rhs);

        (quotient, remainder, lhs_sgn)
    }

    /// Compute the quotient and remainder of `self / rhs`.
    ///
    /// Example:
    /// ```
    /// use crypto_bigint::{I128, NonZero, U128};
    /// let (quotient, remainder) = I128::from(8).div_rem_uint(&U128::from(3u32).to_nz().unwrap());
    /// assert_eq!(quotient, I128::from(2));
    /// assert_eq!(remainder, I128::from(2));
    ///
    /// let (quotient, remainder) = I128::from(-8).div_rem_uint(&U128::from(3u32).to_nz().unwrap());
    /// assert_eq!(quotient, I128::from(-2));
    /// assert_eq!(remainder, I128::from(-2));
    /// ```
    pub const fn div_rem_uint(&self, rhs: &NonZero<Uint<LIMBS>>) -> (Self, Self) {
        let (quotient, remainder, lhs_sgn) = self.div_rem_base_uint(rhs);
        (
            Self(quotient).wrapping_neg_if(lhs_sgn),
            Self(remainder).wrapping_neg_if(lhs_sgn),
        )
    }

    /// Perform division.
    /// Note: this operation rounds towards zero, truncating any fractional part of the exact result.
    pub fn div_uint(&self, rhs: &Uint<LIMBS>) -> CtOption<Self> {
        NonZero::new(*rhs).map(|rhs| self.div_rem_uint(&rhs).0)
    }

    /// Perform checked division.
    /// Note: this operation rounds down.
    ///
    /// Example:
    /// ```
    /// use crypto_bigint::{I128, U128};
    /// assert_eq!(
    ///     I128::from(8).div_floor_uint(&U128::from(3u32)).unwrap(),
    ///     I128::from(2)
    /// );
    /// assert_eq!(
    ///     I128::from(-8).div_floor_uint(&U128::from(3u32)).unwrap(),
    ///     I128::from(-3)
    /// );
    /// ```
    pub fn div_floor_uint(&self, rhs: &Uint<LIMBS>) -> CtOption<Self> {
        NonZero::new(*rhs).and_then(|rhs| {
            let (quotient, remainder, lhs_sgn) = self.div_rem_base_uint(&rhs);

            // Increment the quotient when
            // - lhs is negative, and
            // - there is a non-zero remainder.
            let increment_quotient = remainder.is_nonzero().and(lhs_sgn);
            let quotient_sub_one = quotient.wrapping_add(&Uint::ONE);
            let quotient = Uint::select(&quotient, &quotient_sub_one, increment_quotient);

            Self::new_from_abs_sign(quotient, lhs_sgn).into()
        })
    }

    /// Perform checked division and mod.
    /// Note: this operation rounds down.
    ///
    /// Example:
    /// ```
    /// use crypto_bigint::{I128, U128};
    /// assert_eq!(
    ///     I128::from(8).div_rem_floor_uint(&U128::from(3u32)).unwrap(),
    ///     (I128::from(2), I128::from(2))
    /// );
    /// assert_eq!(
    ///     I128::from(-8).div_rem_floor_uint(&U128::from(3u32)).unwrap(),
    ///     (I128::from(-3), I128::from(-1))
    /// );
    /// ```
    pub fn div_rem_floor_uint(&self, rhs: &Uint<LIMBS>) -> CtOption<(Self, Self)> {
        let (lhs_mag, lhs_sgn) = self.abs_sign();
        NonZero::new(*rhs).and_then(|rhs| {
            let (quotient, remainder) = lhs_mag.div_rem(&rhs);

            // Increase the quotient by one when lhs and rhs have opposing signs and there
            // is a non-zero remainder.
            let modify = remainder.is_nonzero().and(lhs_sgn);
            let quotient_sub_one = quotient.wrapping_add(&Uint::ONE);
            let quotient = Uint::select(&quotient, &quotient_sub_one, modify);

            // Invert the remainder and add one to remainder when lhs and rhs have opposing signs
            // and the remainder is non-zero.
            let inv_remainder = rhs.wrapping_sub(&remainder);
            let remainder = Uint::select(&remainder, &inv_remainder, modify);

            CtOption::from(Int::new_from_abs_sign(quotient, lhs_sgn)).and_then(|quotient| {
                CtOption::from(Int::new_from_abs_sign(remainder, lhs_sgn))
                    .and_then(|remainder| CtOption::new((quotient, remainder), Choice::from(1u8)))
            })
        })
    }
}

impl<const LIMBS: usize> Div<&NonZero<Uint<LIMBS>>> for &Int<LIMBS> {
    type Output = Int<LIMBS>;

    fn div(self, rhs: &NonZero<Uint<LIMBS>>) -> Self::Output {
        *self / *rhs
    }
}

impl<const LIMBS: usize> Div<&NonZero<Uint<LIMBS>>> for Int<LIMBS> {
    type Output = Int<LIMBS>;

    fn div(self, rhs: &NonZero<Uint<LIMBS>>) -> Self::Output {
        self / *rhs
    }
}

impl<const LIMBS: usize> Div<NonZero<Uint<LIMBS>>> for &Int<LIMBS> {
    type Output = Int<LIMBS>;

    fn div(self, rhs: NonZero<Uint<LIMBS>>) -> Self::Output {
        *self / rhs
    }
}

impl<const LIMBS: usize> Div<NonZero<Uint<LIMBS>>> for Int<LIMBS> {
    type Output = Int<LIMBS>;

    fn div(self, rhs: NonZero<Uint<LIMBS>>) -> Self::Output {
        self.div_rem_uint(&rhs).0
    }
}

#[cfg(test)]
mod tests {
    use crate::{I128, U128};

    #[test]
    fn test_div_uint() {
        // lhs = min
        assert_eq!(I128::MIN / U128::ONE.to_nz().unwrap(), I128::MIN);
        assert_eq!(I128::MIN / U128::MAX.to_nz().unwrap(), I128::ZERO);

        // lhs = -1
        assert_eq!(
            I128::MINUS_ONE / U128::ONE.to_nz().unwrap(),
            I128::MINUS_ONE
        );
        assert_eq!(I128::MINUS_ONE / U128::MAX.to_nz().unwrap(), I128::ZERO);

        // lhs = 0
        assert_eq!(I128::ZERO / U128::ONE.to_nz().unwrap(), I128::ZERO);
        assert_eq!(I128::ZERO / U128::MAX.to_nz().unwrap(), I128::ZERO);

        // lhs = 1
        assert_eq!(I128::ONE / U128::ONE.to_nz().unwrap(), I128::ONE);
        assert_eq!(I128::ONE / U128::MAX.to_nz().unwrap(), I128::ZERO);

        // lhs = max
        assert_eq!(I128::MAX / U128::ONE.to_nz().unwrap(), I128::MAX);
        assert_eq!(I128::MAX / U128::MAX.to_nz().unwrap(), I128::ZERO);
    }
}
