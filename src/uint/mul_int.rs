use crate::{ConstChoice, Int, Uint};

impl<const LIMBS: usize> Uint<LIMBS> {
    /// Compute "wide" multiplication between an [`Uint`] and [`Int`] as 3-tuple `(lo, hi, negate)`.
    /// The `(lo, hi)` components contain the _magnitude of the product_, with sizes
    /// corresponding to the sizes of the operands; `negate` indicates whether the result should be
    /// negated when converted from [`Uint`] to [`Int`].
    ///
    /// Note: even if `negate` is truthy, the magnitude might be zero!
    pub const fn widening_mul_int<const RHS_LIMBS: usize>(
        &self,
        rhs: &Int<RHS_LIMBS>,
    ) -> (Uint<LIMBS>, Uint<RHS_LIMBS>, ConstChoice) {
        let (rhs_abs, rhs_sgn) = rhs.abs_sign();
        let (lo, hi) = self.widening_mul(&rhs_abs);
        (lo, hi, rhs_sgn)
    }
}

#[cfg(test)]
mod tests {
    use crate::{ConstChoice, I64, U64, U128};

    #[test]
    fn widening_mul_int() {
        assert_eq!(
            U128::MAX.widening_mul_int(&I64::from_i64(-55)),
            (
                U128::from_be_hex("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFC9"),
                U64::from_u64(54),
                ConstChoice::TRUE
            )
        )
    }
}
