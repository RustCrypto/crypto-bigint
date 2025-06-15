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

    /// Swap the rows of this matrix if `swap` is truthy. Otherwise, do nothing.
    #[inline]
    pub(crate) const fn conditional_swap_rows(&mut self, swap: ConstChoice) {
        Int::conditional_swap(&mut self.m00, &mut self.m10, swap);
        Int::conditional_swap(&mut self.m01, &mut self.m11, swap);
    }

    /// Subtract the bottom row from the top if `subtract` is truthy. Otherwise, do nothing.
    #[inline]
    pub(crate) const fn conditional_subtract_bottom_row_from_top(&mut self, subtract: ConstChoice) {
        self.m00 = Int::select(&self.m00, &self.m00.wrapping_sub(&self.m10), subtract);
        self.m01 = Int::select(&self.m01, &self.m01.wrapping_sub(&self.m11), subtract);
    }

    /// Double the bottom row of this matrix if `double` is truthy. Otherwise, do nothing.
    #[inline]
    pub(crate) const fn conditional_double_bottom_row(&mut self, double: ConstChoice) {
        // safe to vartime; shr_vartime is variable in the value of shift only. Since this shift
        // is a public constant, the constant time property of this algorithm is not impacted.
        self.m10 = Int::select(&self.m10, &self.m10.shl_vartime(1), double);
        self.m11 = Int::select(&self.m11, &self.m11.shl_vartime(1), double);
    }
}

#[cfg(test)]
mod tests {
    use crate::uint::bingcd::matrix::IntMatrix;
    use crate::{ConstChoice, Int, U256};

    const X: IntMatrix<{ U256::LIMBS }> = IntMatrix::new(
        Int::from_i64(1i64),
        Int::from_i64(7i64),
        Int::from_i64(23i64),
        Int::from_i64(53i64),
    );

    #[test]
    fn test_conditional_swap() {
        let mut y = X;
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
        let mut y = X;
        y.conditional_subtract_bottom_row_from_top(ConstChoice::FALSE);
        assert_eq!(y, X);
        y.conditional_subtract_bottom_row_from_top(ConstChoice::TRUE);
        assert_eq!(
            y,
            IntMatrix::new(
                Int::from(-22i32),
                Int::from(-46i32),
                Int::from(23i32),
                Int::from(53i32)
            )
        );
    }

    #[test]
    fn test_conditional_double() {
        let mut y = X;
        y.conditional_double_bottom_row(ConstChoice::FALSE);
        assert_eq!(y, X);
        y.conditional_double_bottom_row(ConstChoice::TRUE);
        assert_eq!(
            y,
            IntMatrix::new(
                Int::from(1i32),
                Int::from(7i32),
                Int::from(46i32),
                Int::from(106i32),
            )
        );
    }
}
