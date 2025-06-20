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
        self.m00 = self
            .m00
            .wrapping_sub(&Int::select(&Int::ZERO, &self.m10, subtract));
        self.m01 = self
            .m01
            .wrapping_sub(&Int::select(&Int::ZERO, &self.m11, subtract));
    }

    /// Double the bottom row of this matrix if `double` is truthy. Otherwise, do nothing.
    #[inline]
    pub(crate) const fn conditional_double_bottom_row(&mut self, double: ConstChoice) {
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
        pub(crate) const fn new_i64(
            matrix: (i64, i64, i64, i64),
            k: u32,
            k_upper_bound: u32,
        ) -> Self {
            Self {
                m00: Int::from_i64(matrix.0),
                m01: Int::from_i64(matrix.1),
                m10: Int::from_i64(matrix.2),
                m11: Int::from_i64(matrix.3),
                k,
                k_upper_bound,
            }
        }

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

    const X: BinXgcdMatrix<{ U256::LIMBS }> = BinXgcdMatrix::new_i64((1, 7, 23, 53), 6, 8);

    #[test]
    fn test_wrapping_apply_to() {
        let a = U64::from_be_hex("CA048AFA63CD6A1F");
        let b = U64::from_be_hex("AE693BF7BE8E5566");
        let matrix = BinXgcdMatrix::<{ I64::LIMBS }>::new_i64((288, -208, -310, 679), 17, 17);

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
        let target = BinXgcdMatrix::new_i64((23, 53, 1, 7), 6, 8);
        assert_eq!(y, target);
    }

    #[test]
    fn test_conditional_swap() {
        let mut y = X;
        y.conditional_swap_rows(ConstChoice::FALSE);
        assert_eq!(y, X);
        y.conditional_swap_rows(ConstChoice::TRUE);
        let target = BinXgcdMatrix::new_i64((23, 53, 1, 7), 6, 8);
        assert_eq!(y, target);
    }

    #[test]
    fn test_conditional_subtract() {
        let mut y = X;
        y.conditional_subtract_bottom_row_from_top(ConstChoice::FALSE);
        assert_eq!(y, X);
        y.conditional_subtract_bottom_row_from_top(ConstChoice::TRUE);
        let target = BinXgcdMatrix::new_i64((-22, -46, 23, 53), 6, 8);
        assert_eq!(y, target);
    }

    #[test]
    fn test_conditional_double() {
        let mut y = X;
        y.conditional_double_bottom_row(ConstChoice::FALSE);
        let target = BinXgcdMatrix::new_i64((1, 7, 23, 53), 6, 9);
        assert_eq!(y, target);
        y.conditional_double_bottom_row(ConstChoice::TRUE);
        let target = BinXgcdMatrix::new_i64((1, 7, 46, 106), 7, 10);
        assert_eq!(y, target);
    }
}
