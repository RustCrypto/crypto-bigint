//! [`Int`] multiplication operations.

use core::ops::{Mul, MulAssign};

use subtle::CtOption;

use crate::{Checked, CheckedMul, ConcatMixed, ConstChoice, ConstCtOption, Int, Uint, Zero};

impl<const LIMBS: usize> Int<LIMBS> {
    /// Compute "wide" multiplication as a 3-tuple `(lo, hi, negate)`.
    /// The `(lo, hi)` components contain the _magnitude of the product_, with sizes
    /// corresponding to the sizes of the operands; `negate` indicates whether the result should be
    /// negated when converted from [`Uint`] to [`Int`].
    ///
    /// Note: even if `negate` is truthy, the magnitude might be zero!
    pub const fn split_mul<const RHS_LIMBS: usize>(
        &self,
        rhs: &Int<RHS_LIMBS>,
    ) -> (Uint<{ LIMBS }>, Uint<{ RHS_LIMBS }>, ConstChoice) {
        // Step 1: split operands into their signs and magnitudes.
        let (lhs_abs, lhs_sgn) = self.abs_sign();
        let (rhs_abs, rhs_sgn) = rhs.abs_sign();

        // Step 2: multiply the magnitudes
        let (lo, hi) = lhs_abs.split_mul(&rhs_abs);

        // Step 3. Determine if the result should be negated.
        // This should be done if and only if lhs and rhs have opposing signs.
        // Note: if either operand is zero, the resulting magnitude will also be zero. Negating
        // zero, however, still yields zero, so having a truthy `negate` in that scenario is OK.
        let negate = lhs_sgn.xor(rhs_sgn);

        (lo, hi, negate)
    }

    /// Multiply `self` by `rhs`, returning a concatenated "wide" result.
    pub const fn widening_mul<const RHS_LIMBS: usize, const WIDE_LIMBS: usize>(
        &self,
        rhs: &Int<RHS_LIMBS>,
    ) -> Int<WIDE_LIMBS>
    where
        Uint<LIMBS>: ConcatMixed<Uint<RHS_LIMBS>, MixedOutput = Uint<WIDE_LIMBS>>,
    {
        let (lhs_abs, lhs_sign) = self.abs_sign();
        let (rhs_abs, rhs_sign) = rhs.abs_sign();
        let product_abs = lhs_abs.widening_mul(&rhs_abs);
        let product_sign = lhs_sign.xor(rhs_sign);

        // always fits
        Int::from_bits(product_abs.wrapping_neg_if(product_sign))
    }
}

/// Squaring operations.
impl<const LIMBS: usize> Int<LIMBS> {
    /// Square self, returning a concatenated "wide" result.
    pub fn widening_square<const WIDE_LIMBS: usize>(&self) -> Uint<WIDE_LIMBS>
    where
        Uint<LIMBS>: ConcatMixed<Uint<LIMBS>, MixedOutput = Uint<WIDE_LIMBS>>,
    {
        self.abs().widening_square()
    }

    /// Square self, checking that the result fits in the original [`Uint`] size.
    pub fn checked_square(&self) -> ConstCtOption<Uint<LIMBS>> {
        self.abs().checked_square()
    }

    /// Perform wrapping square, discarding overflow.
    pub const fn wrapping_square(&self) -> Uint<LIMBS> {
        self.abs().wrapping_square()
    }

    /// Perform saturating squaring, returning `MAX` on overflow.
    pub const fn saturating_square(&self) -> Uint<LIMBS> {
        self.abs().saturating_square()
    }
}

impl<const LIMBS: usize, const RHS_LIMBS: usize> CheckedMul<Int<RHS_LIMBS>> for Int<LIMBS> {
    #[inline]
    fn checked_mul(&self, rhs: &Int<RHS_LIMBS>) -> CtOption<Self> {
        let (lo, hi, is_negative) = self.split_mul(rhs);
        let val = Self::new_from_abs_sign(lo, is_negative);
        CtOption::from(val).and_then(|int| CtOption::new(int, hi.is_zero()))
    }
}

impl<const LIMBS: usize, const RHS_LIMBS: usize> Mul<Int<RHS_LIMBS>> for Int<LIMBS> {
    type Output = Int<LIMBS>;

    fn mul(self, rhs: Int<RHS_LIMBS>) -> Self {
        self.mul(&rhs)
    }
}

impl<const LIMBS: usize, const RHS_LIMBS: usize> Mul<&Int<RHS_LIMBS>> for Int<LIMBS> {
    type Output = Int<LIMBS>;

    fn mul(self, rhs: &Int<RHS_LIMBS>) -> Self {
        (&self).mul(rhs)
    }
}

impl<const LIMBS: usize, const RHS_LIMBS: usize> Mul<Int<RHS_LIMBS>> for &Int<LIMBS> {
    type Output = Int<LIMBS>;

    fn mul(self, rhs: Int<RHS_LIMBS>) -> Self::Output {
        self.mul(&rhs)
    }
}

impl<const LIMBS: usize, const RHS_LIMBS: usize> Mul<&Int<RHS_LIMBS>> for &Int<LIMBS> {
    type Output = Int<LIMBS>;

    fn mul(self, rhs: &Int<RHS_LIMBS>) -> Self::Output {
        self.checked_mul(rhs)
            .expect("attempted to multiply with overflow")
    }
}

impl<const LIMBS: usize> MulAssign<Checked<Int<LIMBS>>> for Checked<Int<LIMBS>> {
    fn mul_assign(&mut self, other: Checked<Int<LIMBS>>) {
        *self = *self * other;
    }
}

impl<const LIMBS: usize> MulAssign<&Checked<Int<LIMBS>>> for Checked<Int<LIMBS>> {
    fn mul_assign(&mut self, other: &Checked<Int<LIMBS>>) {
        *self = *self * other;
    }
}

// TODO(lleoha): unfortunately we cannot satisfy this (yet!).
// impl<const LIMBS: usize, const RHS_LIMBS: usize, const WIDE_LIMBS: usize>
// WideningMul<Int<RHS_LIMBS>> for Int<LIMBS>
// where
//     Uint<LIMBS>: ConcatMixed<Uint<RHS_LIMBS>, MixedOutput = Uint<WIDE_LIMBS>>,
// {
//     type Output = Int<WIDE_LIMBS>;
//
//     #[inline]
//     fn widening_mul(&self, rhs: Int<RHS_LIMBS>) -> Self::Output {
//         self.widening_mul(&rhs)
//     }
// }

#[cfg(test)]
mod tests {
    use crate::{CheckedMul, ConstChoice, I128, I256, Int, U128, U256};

    #[test]
    fn test_checked_mul() {
        let min_plus_one = Int {
            0: I128::MIN.0.wrapping_add(&I128::ONE.0),
        };

        // lhs = min

        let result = I128::MIN.checked_mul(&I128::MIN);
        assert!(bool::from(result.is_none()));

        let result = I128::MIN.checked_mul(&I128::MINUS_ONE);
        assert!(bool::from(result.is_none()));

        let result = I128::MIN.checked_mul(&I128::ZERO);
        assert_eq!(result.unwrap(), I128::ZERO);

        let result = I128::MIN.checked_mul(&I128::ONE);
        assert_eq!(result.unwrap(), I128::MIN);

        let result = I128::MIN.checked_mul(&I128::MAX);
        assert!(bool::from(result.is_none()));

        // lhs = -1

        let result = I128::MINUS_ONE.checked_mul(&I128::MIN);
        assert!(bool::from(result.is_none()));

        let result = I128::MINUS_ONE.checked_mul(&I128::MINUS_ONE);
        assert_eq!(result.unwrap(), I128::ONE);

        let result = I128::MINUS_ONE.checked_mul(&I128::ZERO);
        assert_eq!(result.unwrap(), I128::ZERO);

        let result = I128::MINUS_ONE.checked_mul(&I128::ONE);
        assert_eq!(result.unwrap(), I128::MINUS_ONE);

        let result = I128::MINUS_ONE.checked_mul(&I128::MAX);
        assert_eq!(result.unwrap(), min_plus_one);

        // lhs = 0

        let result = I128::ZERO.checked_mul(&I128::MIN);
        assert_eq!(result.unwrap(), I128::ZERO);

        let result = I128::ZERO.checked_mul(&I128::MINUS_ONE);
        assert_eq!(result.unwrap(), I128::ZERO);

        let result = I128::ZERO.checked_mul(&I128::ZERO);
        assert_eq!(result.unwrap(), I128::ZERO);

        let result = I128::ZERO.checked_mul(&I128::ONE);
        assert_eq!(result.unwrap(), I128::ZERO);

        let result = I128::ZERO.checked_mul(&I128::MAX);
        assert_eq!(result.unwrap(), I128::ZERO);

        // lhs = 1

        let result = I128::ONE.checked_mul(&I128::MIN);
        assert_eq!(result.unwrap(), I128::MIN);

        let result = I128::ONE.checked_mul(&I128::MINUS_ONE);
        assert_eq!(result.unwrap(), I128::MINUS_ONE);

        let result = I128::ONE.checked_mul(&I128::ZERO);
        assert_eq!(result.unwrap(), I128::ZERO);

        let result = I128::ONE.checked_mul(&I128::ONE);
        assert_eq!(result.unwrap(), I128::ONE);

        let result = I128::ONE.checked_mul(&I128::MAX);
        assert_eq!(result.unwrap(), I128::MAX);

        // lhs = max

        let result = I128::MAX.checked_mul(&I128::MIN);
        assert!(bool::from(result.is_none()));

        let result = I128::MAX.checked_mul(&I128::MINUS_ONE);
        assert_eq!(result.unwrap(), min_plus_one);

        let result = I128::MAX.checked_mul(&I128::ZERO);
        assert_eq!(result.unwrap(), I128::ZERO);

        let result = I128::MAX.checked_mul(&I128::ONE);
        assert_eq!(result.unwrap(), I128::MAX);

        let result = I128::MAX.checked_mul(&I128::MAX);
        assert!(bool::from(result.is_none()));
    }

    #[test]
    fn test_widening_mul() {
        assert_eq!(
            I128::MIN.widening_mul(&I128::MIN),
            I256::from_be_hex("4000000000000000000000000000000000000000000000000000000000000000")
        );
        assert_eq!(
            I128::MIN.widening_mul(&I128::MINUS_ONE),
            I256::from_be_hex("0000000000000000000000000000000080000000000000000000000000000000")
        );
        assert_eq!(I128::MIN.widening_mul(&I128::ZERO), I256::ZERO);
        assert_eq!(
            I128::MIN.widening_mul(&I128::ONE),
            I256::from_be_hex("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF80000000000000000000000000000000")
        );
        assert_eq!(
            I128::MIN.widening_mul(&I128::MAX),
            I256::from_be_hex("C000000000000000000000000000000080000000000000000000000000000000")
        );

        assert_eq!(
            I128::MINUS_ONE.widening_mul(&I128::MIN),
            I256::from_be_hex("0000000000000000000000000000000080000000000000000000000000000000")
        );
        assert_eq!(I128::MINUS_ONE.widening_mul(&I128::MINUS_ONE), I256::ONE);
        assert_eq!(I128::MINUS_ONE.widening_mul(&I128::ZERO), I256::ZERO);
        assert_eq!(I128::MINUS_ONE.widening_mul(&I128::ONE), I256::MINUS_ONE);
        assert_eq!(
            I128::MINUS_ONE.widening_mul(&I128::MAX),
            I256::from_be_hex("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF80000000000000000000000000000001")
        );

        assert_eq!(I128::ZERO.widening_mul(&I128::MIN), I256::ZERO);
        assert_eq!(I128::ZERO.widening_mul(&I128::MINUS_ONE), I256::ZERO);
        assert_eq!(I128::ZERO.widening_mul(&I128::ZERO), I256::ZERO);
        assert_eq!(I128::ZERO.widening_mul(&I128::ONE), I256::ZERO);
        assert_eq!(I128::ZERO.widening_mul(&I128::MAX), I256::ZERO);

        assert_eq!(
            I128::ONE.widening_mul(&I128::MIN),
            I256::from_be_hex("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF80000000000000000000000000000000")
        );
        assert_eq!(I128::ONE.widening_mul(&I128::MINUS_ONE), I256::MINUS_ONE);
        assert_eq!(I128::ONE.widening_mul(&I128::ZERO), I256::ZERO);
        assert_eq!(I128::ONE.widening_mul(&I128::ONE), I256::ONE);
        assert_eq!(
            I128::ONE.widening_mul(&I128::MAX),
            I256::from_be_hex("000000000000000000000000000000007FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF")
        );

        assert_eq!(
            I128::MAX.widening_mul(&I128::MIN),
            I256::from_be_hex("C000000000000000000000000000000080000000000000000000000000000000")
        );
        assert_eq!(
            I128::MAX.widening_mul(&I128::MINUS_ONE),
            I256::from_be_hex("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF80000000000000000000000000000001")
        );
        assert_eq!(I128::MAX.widening_mul(&I128::ZERO), I256::ZERO);
        assert_eq!(
            I128::MAX.widening_mul(&I128::ONE),
            I256::from_be_hex("000000000000000000000000000000007FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF")
        );
        assert_eq!(
            I128::MAX.widening_mul(&I128::MAX),
            I256::from_be_hex("3FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF00000000000000000000000000000001")
        );
    }

    #[test]
    fn test_widening_square() {
        let res = I128::from_i64(i64::MIN).widening_square();
        assert_eq!(
            res,
            U256::from_be_hex("0000000000000000000000000000000040000000000000000000000000000000")
        );

        let x: I128 = I128::MINUS_ONE << 64;
        let res = x.widening_square();
        assert_eq!(
            res,
            U256::from_be_hex("0000000000000000000000000000000100000000000000000000000000000000")
        )
    }

    #[test]
    fn test_checked_square() {
        let res = I128::from_i64(i64::MIN).checked_square();
        assert_eq!(res.is_some(), ConstChoice::TRUE);
        assert_eq!(
            res.unwrap(),
            U128::from_be_hex("40000000000000000000000000000000")
        );

        let x: I128 = I128::MINUS_ONE << 64;
        let res = x.checked_square();
        assert_eq!(res.is_none(), ConstChoice::TRUE)
    }

    #[test]
    fn test_wrapping_square() {
        let res = I128::from_i64(i64::MIN).wrapping_square();
        assert_eq!(res, U128::from_be_hex("40000000000000000000000000000000"));

        let x: I128 = I128::MINUS_ONE << 64;
        let res = x.wrapping_square();
        assert_eq!(res, U128::ZERO);

        let x: I128 = I128::from_i64(i64::MAX);
        let res = x.wrapping_square();
        assert_eq!(res, U128::from_be_hex("3FFFFFFFFFFFFFFF0000000000000001"))
    }

    #[test]
    fn test_saturating_square() {
        assert_eq!(
            I128::from_i64(i64::MIN).saturating_square(),
            U128::from_be_hex("40000000000000000000000000000000")
        );
        let x: I128 = I128::MINUS_ONE << 64;
        assert_eq!(x.saturating_square(), U128::MAX);
    }
}
