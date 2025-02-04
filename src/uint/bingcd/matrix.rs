use crate::uint::bingcd::extension::ExtendedInt;
use crate::{ConstChoice, Int, Uint};

type Vector<T> = (T, T);

#[derive(Debug, Clone, Copy, PartialEq)]
pub(crate) struct IntMatrix<const LIMBS: usize> {
    m00: Int<LIMBS>,
    m01: Int<LIMBS>,
    m10: Int<LIMBS>,
    m11: Int<LIMBS>,
}

impl<const LIMBS: usize> IntMatrix<LIMBS> {
    /// The unit matrix.
    pub(crate) const UNIT: Self = Self::new(Int::ONE, Int::ZERO, Int::ZERO, Int::ONE);

    pub(crate) const fn new(
        m00: Int<LIMBS>,
        m01: Int<LIMBS>,
        m10: Int<LIMBS>,
        m11: Int<LIMBS>,
    ) -> Self {
        Self { m00, m01, m10, m11 }
    }

    /// Apply this matrix to a vector of [Uint]s, returning the result as a vector of
    /// [ExtendedInt]s.
    #[inline]
    pub(crate) const fn extended_apply_to<const VEC_LIMBS: usize>(
        &self,
        vec: Vector<Uint<VEC_LIMBS>>,
    ) -> Vector<ExtendedInt<VEC_LIMBS, LIMBS>> {
        let (a, b) = vec;
        let a0 = ExtendedInt::from_product(a, self.m00);
        let a1 = ExtendedInt::from_product(a, self.m10);
        let b0 = ExtendedInt::from_product(b, self.m01);
        let b1 = ExtendedInt::from_product(b, self.m11);
        (a0.wrapping_add(&b0), a1.wrapping_add(&b1))
    }

    /// Apply this matrix to `rhs`. Panics if a multiplication overflows.
    /// TODO: consider implementing (a variation to) Strassen. Doing so will save a multiplication.
    #[inline]
    const fn checked_mul<const RHS_LIMBS: usize>(&self, rhs: &IntMatrix<RHS_LIMBS>) -> Self {
        let a0 = self.m00.const_checked_mul(&rhs.m00).expect("no overflow");
        let a1 = self.m01.const_checked_mul(&rhs.m10).expect("no overflow");
        let a = a0.checked_add(&a1).expect("no overflow");
        let b0 = self.m00.const_checked_mul(&rhs.m01).expect("no overflow");
        let b1 = self.m01.const_checked_mul(&rhs.m11).expect("no overflow");
        let b = b0.checked_add(&b1).expect("no overflow");
        let c0 = self.m10.const_checked_mul(&rhs.m00).expect("no overflow");
        let c1 = self.m11.const_checked_mul(&rhs.m10).expect("no overflow");
        let c = c0.checked_add(&c1).expect("no overflow");
        let d0 = self.m10.const_checked_mul(&rhs.m01).expect("no overflow");
        let d1 = self.m11.const_checked_mul(&rhs.m11).expect("no overflow");
        let d = d0.checked_add(&d1).expect("no overflow");
        IntMatrix::new(a, b, c, d)
    }

    /// Swap the rows of this matrix if `swap` is truthy. Otherwise, do nothing.
    #[inline]
    pub(crate) const fn conditional_swap_rows(&mut self, swap: ConstChoice) {
        Int::conditional_swap(&mut self.m00, &mut self.m10, swap);
        Int::conditional_swap(&mut self.m01, &mut self.m11, swap);
    }

    /// Subtract the bottom row from the top if `subtract` is truthy. Otherwise, do nothing.
    #[inline]
    pub(crate) const fn conditional_subtract_top_row_from_bottom(&mut self, subtract: ConstChoice) {
        self.m10 = Int::select(&self.m10, &self.m10.wrapping_sub(&self.m00), subtract);
        self.m11 = Int::select(&self.m11, &self.m11.wrapping_sub(&self.m01), subtract);
    }

    /// Double the right column of this matrix if `double` is truthy. Otherwise, do nothing.
    #[inline]
    pub(crate) const fn conditional_double_top_row(&mut self, double: ConstChoice) {
        self.m00 = Int::select(&self.m00, &self.m00.shl_vartime(1), double);
        self.m01 = Int::select(&self.m01, &self.m01.shl_vartime(1), double);
    }
}

#[cfg(test)]
mod tests {
    use crate::uint::bingcd::matrix::IntMatrix;
    use crate::{ConstChoice, Int, I256, U256};

    const X: IntMatrix<{ U256::LIMBS }> = IntMatrix::new(
        Int::from_i64(1i64),
        Int::from_i64(7i64),
        Int::from_i64(23i64),
        Int::from_i64(53i64),
    );

    #[test]
    fn test_conditional_swap() {
        let mut y = X.clone();
        y.conditional_swap_rows(ConstChoice::FALSE);
        assert_eq!(y, X);
        y.conditional_swap_rows(ConstChoice::TRUE);
        assert_eq!(
            y,
            IntMatrix::new(
                Int::from(23i32),
                Int::from(53i32),
                Int::from(1i32),
                Int::from(7i32)
            )
        );
    }

    #[test]
    fn test_conditional_subtract() {
        let mut y = X.clone();
        y.conditional_subtract_top_row_from_bottom(ConstChoice::FALSE);
        assert_eq!(y, X);
        y.conditional_subtract_top_row_from_bottom(ConstChoice::TRUE);
        assert_eq!(
            y,
            IntMatrix::new(
                Int::from(1i32),
                Int::from(7i32),
                Int::from(22i32),
                Int::from(46i32)
            )
        );
    }

    #[test]
    fn test_conditional_double() {
        let mut y = X.clone();
        y.conditional_double_top_row(ConstChoice::FALSE);
        assert_eq!(y, X);
        y.conditional_double_top_row(ConstChoice::TRUE);
        assert_eq!(
            y,
            IntMatrix::new(
                Int::from(2i32),
                Int::from(14i32),
                Int::from(23i32),
                Int::from(53i32),
            )
        );
    }

    #[test]
    fn test_checked_mul() {
        let res = X.checked_mul(&X);
        assert_eq!(
            res,
            IntMatrix::new(
                I256::from_i64(162i64),
                I256::from_i64(378i64),
                I256::from_i64(1242i64),
                I256::from_i64(2970i64),
            )
        )
    }
}
