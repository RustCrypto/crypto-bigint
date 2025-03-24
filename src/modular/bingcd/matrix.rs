use crate::modular::bingcd::extension::ExtendedInt;
use crate::{ConstChoice, Int, Uint};

type Vector<T> = (T, T);

#[derive(Debug, Clone, Copy, PartialEq)]
pub(crate) struct BinXgcdMatrix<const LIMBS: usize> {
    m00: Int<LIMBS>,
    m01: Int<LIMBS>,
    m10: Int<LIMBS>,
    m11: Int<LIMBS>,
    k: u32,
    k_upper_bound: u32,
}

impl<const LIMBS: usize> BinXgcdMatrix<LIMBS> {
    /// The unit matrix.
    pub(crate) const UNIT: Self = Self::new(Int::ONE, Int::ZERO, Int::ZERO, Int::ONE, 0, 0);

    pub(crate) const fn new(
        m00: Int<LIMBS>,
        m01: Int<LIMBS>,
        m10: Int<LIMBS>,
        m11: Int<LIMBS>,
        k: u32,
        k_upper_bound: u32,
    ) -> Self {
        Self {
            m00,
            m01,
            m10,
            m11,
            k,
            k_upper_bound,
        }
    }

    /// Apply this matrix to a vector of [Uint]s, returning the result as a vector of
    /// [ExtendedInt]s.
    #[inline]
    pub(crate) const fn extended_apply_to<const VEC_LIMBS: usize>(
        &self,
        vec: Vector<Uint<VEC_LIMBS>>,
    ) -> Vector<ExtendedInt<VEC_LIMBS, LIMBS>> {
        let (a, b) = vec;
        let m00a = ExtendedInt::from_product(a, self.m00);
        let m10a = ExtendedInt::from_product(a, self.m10);
        let m01b = ExtendedInt::from_product(b, self.m01);
        let m11b = ExtendedInt::from_product(b, self.m11);
        (
            m00a.wrapping_add(&m01b).div_2k(self.k),
            m11b.wrapping_add(&m10a).div_2k(self.k),
        )
    }

    /// Swap the rows of this matrix if `swap` is truthy. Otherwise, do nothing.
    #[inline]
    pub(crate) const fn conditional_swap_rows(&mut self, swap: ConstChoice) {
        Int::conditional_swap(&mut self.m00, &mut self.m10, swap);
        Int::conditional_swap(&mut self.m01, &mut self.m11, swap);
    }

    /// Swap the rows of this matrix.
    #[inline]
    pub(crate) const fn swap_rows(&mut self) {
        self.conditional_swap_rows(ConstChoice::TRUE);
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
        self.m10 = self
            .m10
            .wrapping_add(&Int::select(&Int::ZERO, &self.m10, double));
        self.m11 = self
            .m11
            .wrapping_add(&Int::select(&Int::ZERO, &self.m11, double));
        self.k = double.select_u32(self.k, self.k + 1);
        self.k_upper_bound += 1;
    }
}

#[cfg(test)]
mod tests {
    use crate::modular::bingcd::matrix::BinXgcdMatrix;
    use crate::{ConstChoice, I64, Int, U64, U256, Uint};

    impl<const LIMBS: usize> BinXgcdMatrix<LIMBS> {
        pub(crate) const fn as_elements(
            &self,
        ) -> (&Int<LIMBS>, &Int<LIMBS>, &Int<LIMBS>, &Int<LIMBS>, u32, u32) {
            (
                &self.m00,
                &self.m01,
                &self.m10,
                &self.m11,
                self.k,
                self.k_upper_bound,
            )
        }
    }

    const X: BinXgcdMatrix<{ U256::LIMBS }> = BinXgcdMatrix::new(
        Int::from_i64(1i64),
        Int::from_i64(7i64),
        Int::from_i64(23i64),
        Int::from_i64(53i64),
        6,
        8,
    );

    #[test]
    fn test_wrapping_apply_to() {
        let a = U64::from_be_hex("CA048AFA63CD6A1F");
        let b = U64::from_be_hex("AE693BF7BE8E5566");
        let matrix = BinXgcdMatrix {
            m00: I64::from_be_hex("0000000000000120"),
            m01: I64::from_be_hex("FFFFFFFFFFFFFF30"),
            m10: I64::from_be_hex("FFFFFFFFFFFFFECA"),
            m11: I64::from_be_hex("00000000000002A7"),
            k: 17,
            k_upper_bound: 17,
        };

        let (a_, b_) = matrix.extended_apply_to((a, b));
        assert_eq!(
            a_.wrapping_drop_extension().0,
            Uint::from_be_hex("002AC7CDD032B9B9")
        );
        assert_eq!(
            b_.wrapping_drop_extension().0,
            Uint::from_be_hex("006CFBCEE172C863")
        );
    }

    #[test]
    fn test_swap() {
        let mut y = X;
        y.swap_rows();
        assert_eq!(
            y,
            BinXgcdMatrix::new(
                Int::from(23i32),
                Int::from(53i32),
                Int::from(1i32),
                Int::from(7i32),
                6,
                8
            )
        );
    }

    #[test]
    fn test_conditional_swap() {
        let mut y = X;
        y.conditional_swap_rows(ConstChoice::FALSE);
        assert_eq!(y, X);
        y.conditional_swap_rows(ConstChoice::TRUE);
        assert_eq!(
            y,
            BinXgcdMatrix::new(
                Int::from(23i32),
                Int::from(53i32),
                Int::from(1i32),
                Int::from(7i32),
                6,
                8
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
            BinXgcdMatrix::new(
                Int::from(-22i32),
                Int::from(-46i32),
                Int::from(23i32),
                Int::from(53i32),
                6,
                8
            )
        );
    }

    #[test]
    fn test_conditional_double() {
        let mut y = X;
        y.conditional_double_bottom_row(ConstChoice::FALSE);
        assert_eq!(
            y,
            BinXgcdMatrix::new(
                Int::from_i64(1i64),
                Int::from_i64(7i64),
                Int::from_i64(23i64),
                Int::from_i64(53i64),
                6,
                9
            )
        );
        y.conditional_double_bottom_row(ConstChoice::TRUE);
        assert_eq!(
            y,
            BinXgcdMatrix::new(
                Int::from(1i32),
                Int::from(7i32),
                Int::from(46i32),
                Int::from(106i32),
                7,
                10
            )
        );
    }
}
