use core::ops::Mul;

use subtle::CtOption;

use crate::{CheckedMul, ConcatMixed, ConstChoice, Int, Uint, Zero};

impl<const LIMBS: usize> Int<LIMBS> {
    /// Compute "wide" multiplication between an [`Int`] and [`Uint`] as 3-tuple `(lo, hi, negate)`.
    /// The `(lo, hi)` components contain the _magnitude of the product_, with sizes
    /// corresponding to the sizes of the operands; `negate` indicates whether the result should be
    /// negated when converted from [`Uint`] to [`Int`].
    ///
    /// Note: even if `negate` is truthy, the magnitude might be zero!
    pub const fn split_mul_uint<const RHS_LIMBS: usize>(
        &self,
        rhs: &Uint<RHS_LIMBS>,
    ) -> (Uint<{ LIMBS }>, Uint<{ RHS_LIMBS }>, ConstChoice) {
        // Step 1. split self into its sign and magnitude.
        let (lhs_abs, lhs_sgn) = self.abs_sign();

        // Step 2. Multiply the magnitudes
        let (lo, hi) = lhs_abs.split_mul(&rhs);

        // Step 3. negate if and only if self has a negative sign.
        (lo, hi, lhs_sgn)
    }

    /// Multiply `self` by [`Uint`] `rhs`, returning a concatenated "wide" result.
    pub const fn widening_mul_uint<const RHS_LIMBS: usize, const WIDE_LIMBS: usize>(
        &self,
        rhs: &Uint<RHS_LIMBS>,
    ) -> Int<WIDE_LIMBS>
    where
        Uint<LIMBS>: ConcatMixed<Uint<RHS_LIMBS>, MixedOutput = Uint<WIDE_LIMBS>>,
    {
        let (lhs_abs, lhs_sign) = self.abs_sign();
        let product_abs = lhs_abs.widening_mul(&rhs);

        // always fits
        Int::new_from_uint(product_abs.wrapping_neg_if(lhs_sign))
    }
}

impl<const LIMBS: usize, const RHS_LIMBS: usize> CheckedMul<Uint<RHS_LIMBS>> for Int<LIMBS> {
    #[inline]
    fn checked_mul(&self, rhs: &Uint<RHS_LIMBS>) -> CtOption<Self> {
        let (lo, hi, is_negative) = self.split_mul_uint(rhs);
        let val = Self::new_from_abs_sign(lo, is_negative);
        CtOption::from(val).and_then(|int| CtOption::new(int, hi.is_zero()))
    }
}

impl<const LIMBS: usize, const RHS_LIMBS: usize> Mul<Uint<RHS_LIMBS>> for Int<LIMBS> {
    type Output = Int<LIMBS>;

    fn mul(self, rhs: Uint<RHS_LIMBS>) -> Self {
        self.mul(&rhs)
    }
}

impl<const LIMBS: usize, const RHS_LIMBS: usize> Mul<&Uint<RHS_LIMBS>> for Int<LIMBS> {
    type Output = Int<LIMBS>;

    fn mul(self, rhs: &Uint<RHS_LIMBS>) -> Self {
        (&self).mul(rhs)
    }
}

impl<const LIMBS: usize, const RHS_LIMBS: usize> Mul<Uint<RHS_LIMBS>> for &Int<LIMBS> {
    type Output = Int<LIMBS>;

    fn mul(self, rhs: Uint<RHS_LIMBS>) -> Self::Output {
        self.mul(&rhs)
    }
}

impl<const LIMBS: usize, const RHS_LIMBS: usize> Mul<&Uint<RHS_LIMBS>> for &Int<LIMBS> {
    type Output = Int<LIMBS>;

    fn mul(self, rhs: &Uint<RHS_LIMBS>) -> Self::Output {
        self.checked_mul(rhs)
            .expect("attempted to multiply with overflow")
    }
}

#[cfg(test)]
mod tests {
    use crate::{CheckedMul, I128, I256, U128};

    #[test]
    fn test_checked_mul_uint() {
        // lhs = min

        let result = I128::MIN.checked_mul(&U128::ZERO);
        assert_eq!(result.unwrap(), I128::ZERO);

        let result = I128::MIN.checked_mul(&U128::ONE);
        assert_eq!(result.unwrap(), I128::MIN);

        let result = I128::MIN.checked_mul(&U128::MAX);
        assert!(bool::from(result.is_none()));

        // lhs = -1

        let result = I128::MINUS_ONE.checked_mul(&U128::ZERO);
        assert_eq!(result.unwrap(), I128::ZERO);

        let result = I128::MINUS_ONE.checked_mul(&U128::ONE);
        assert_eq!(result.unwrap(), I128::MINUS_ONE);

        let result = I128::MINUS_ONE.checked_mul(&U128::MAX);
        assert!(bool::from(result.is_none()));

        // lhs = 0

        let result = I128::ZERO.checked_mul(&U128::ZERO);
        assert_eq!(result.unwrap(), I128::ZERO);

        let result = I128::ZERO.checked_mul(&U128::ONE);
        assert_eq!(result.unwrap(), I128::ZERO);

        let result = I128::ZERO.checked_mul(&U128::MAX);
        assert_eq!(result.unwrap(), I128::ZERO);

        // lhs = 1

        let result = I128::ONE.checked_mul(&U128::ZERO);
        assert_eq!(result.unwrap(), I128::ZERO);

        let result = I128::ONE.checked_mul(&U128::ONE);
        assert_eq!(result.unwrap(), I128::ONE);

        let result = I128::ONE.checked_mul(&U128::MAX);
        assert!(bool::from(result.is_none()));

        // lhs = max

        let result = I128::MAX.checked_mul(&U128::ZERO);
        assert_eq!(result.unwrap(), I128::ZERO);

        let result = I128::MAX.checked_mul(&U128::ONE);
        assert_eq!(result.unwrap(), I128::MAX);

        let result = I128::MAX.checked_mul(&U128::MAX);
        assert!(bool::from(result.is_none()));
    }

    #[test]
    fn test_widening_mul_uint() {
        assert_eq!(I128::MIN.widening_mul_uint(&U128::ZERO), I256::ZERO);
        assert_eq!(
            I128::MIN.widening_mul_uint(&U128::ONE),
            I256::from_be_hex("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF80000000000000000000000000000000")
        );
        assert_eq!(
            I128::MIN.widening_mul_uint(&U128::MAX),
            I256::from_be_hex("8000000000000000000000000000000080000000000000000000000000000000")
        );

        assert_eq!(I128::MINUS_ONE.widening_mul_uint(&U128::ZERO), I256::ZERO);
        assert_eq!(
            I128::MINUS_ONE.widening_mul_uint(&U128::ONE),
            I256::MINUS_ONE
        );
        assert_eq!(
            I128::MINUS_ONE.widening_mul_uint(&U128::MAX),
            I256::from_be_hex("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF00000000000000000000000000000001")
        );

        assert_eq!(I128::ZERO.widening_mul_uint(&U128::ZERO), I256::ZERO);
        assert_eq!(I128::ZERO.widening_mul_uint(&U128::ONE), I256::ZERO);
        assert_eq!(I128::ZERO.widening_mul_uint(&U128::MAX), I256::ZERO);

        assert_eq!(I128::ONE.widening_mul_uint(&U128::ZERO), I256::ZERO);
        assert_eq!(I128::ONE.widening_mul_uint(&U128::ONE), I256::ONE);
        assert_eq!(
            I128::ONE.widening_mul_uint(&U128::MAX),
            I256::from_be_hex("00000000000000000000000000000000FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF")
        );

        assert_eq!(I128::MAX.widening_mul_uint(&U128::ZERO), I256::ZERO);
        assert_eq!(
            I128::MAX.widening_mul_uint(&U128::ONE),
            I256::from_be_hex("000000000000000000000000000000007FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF")
        );
        assert_eq!(
            I128::MAX.widening_mul_uint(&U128::MAX),
            I256::from_be_hex("7FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE80000000000000000000000000000001")
        );
    }
}
