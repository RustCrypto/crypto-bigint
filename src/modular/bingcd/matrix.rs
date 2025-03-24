use crate::modular::bingcd::extension::ExtendedInt;
use crate::{ConstChoice, Int, Uint};

type Vector<T> = (T, T);

/// Matrix used to compute the Extended GCD using the Binary Extended GCD algorithm.
///
/// The internal state represents the matrix
/// ```text
/// [ m00 m01 ]
/// [ m10 m11 ] / 2^k
/// ```
///
/// Since some of the operations conditionally increase `k`, this struct furthermore keeps track of
/// `k_upper_bound`; an upper bound on the value of `k`.
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

    pub(crate) const fn as_elements_mut(
        &mut self,
    ) -> (
        &mut Int<LIMBS>,
        &mut Int<LIMBS>,
        &mut Int<LIMBS>,
        &mut Int<LIMBS>,
        &mut u32,
        &mut u32,
    ) {
        (
            &mut self.m00,
            &mut self.m01,
            &mut self.m10,
            &mut self.m11,
            &mut self.k,
            &mut self.k_upper_bound,
        )
    }

    /// Apply this matrix to a vector of [Uint]s, returning the result as a vector of
    /// [ExtendedInt]s.
    #[inline]
    pub(crate) const fn wrapping_apply_to<const VEC_LIMBS: usize>(
        &self,
        vec: Vector<Uint<VEC_LIMBS>>,
    ) -> Vector<ExtendedInt<VEC_LIMBS, LIMBS>> {
        let (a, b) = vec;
        let a0 = ExtendedInt::from_product(a, self.m00);
        let a1 = ExtendedInt::from_product(a, self.m10);
        let b0 = ExtendedInt::from_product(b, self.m01);
        let b1 = ExtendedInt::from_product(b, self.m11);
        (
            a0.wrapping_add(&b0).div_2k(self.k),
            a1.wrapping_add(&b1).div_2k(self.k),
        )
    }

    /// Wrapping apply this matrix to `rhs`. Return the result in `RHS_LIMBS`.
    #[inline]
    pub(crate) const fn wrapping_mul_right<const RHS_LIMBS: usize>(
        &self,
        rhs: &BinXgcdMatrix<RHS_LIMBS>,
    ) -> BinXgcdMatrix<RHS_LIMBS> {
        let a0 = rhs.m00.wrapping_mul(&self.m00);
        let a1 = rhs.m10.wrapping_mul(&self.m01);
        let a = a0.wrapping_add(&a1);
        let b0 = rhs.m01.wrapping_mul(&self.m00);
        let b1 = rhs.m11.wrapping_mul(&self.m01);
        let b = b0.wrapping_add(&b1);
        let c0 = rhs.m00.wrapping_mul(&self.m10);
        let c1 = rhs.m10.wrapping_mul(&self.m11);
        let c = c0.wrapping_add(&c1);
        let d0 = rhs.m01.wrapping_mul(&self.m10);
        let d1 = rhs.m11.wrapping_mul(&self.m11);
        let d = d0.wrapping_add(&d1);
        BinXgcdMatrix::new(
            a,
            b,
            c,
            d,
            self.k + rhs.k,
            self.k_upper_bound + rhs.k_upper_bound,
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
        self.conditional_swap_rows(ConstChoice::TRUE)
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
        self.k = double.select_u32(self.k, self.k + 1);
        self.k_upper_bound += 1;
    }

    /// Negate the elements in the top row if `negate` is truthy. Otherwise, do nothing.
    #[inline]
    pub(crate) const fn conditional_negate_top_row(&mut self, negate: ConstChoice) {
        self.m00 = self.m00.wrapping_neg_if(negate);
        self.m01 = self.m01.wrapping_neg_if(negate);
    }

    /// Negate the elements in the bottom row if `negate` is truthy. Otherwise, do nothing.
    #[inline]
    pub(crate) const fn conditional_negate_bottom_row(&mut self, negate: ConstChoice) {
        self.m10 = self.m10.wrapping_neg_if(negate);
        self.m11 = self.m11.wrapping_neg_if(negate);
    }
}

#[cfg(test)]
mod tests {
    use crate::modular::bingcd::matrix::BinXgcdMatrix;
    use crate::{ConstChoice, I64, I256, Int, U64, Uint};

    const X: BinXgcdMatrix<4> = BinXgcdMatrix::new(
        I256::from_i64(1i64),
        I256::from_i64(7i64),
        I256::from_i64(23i64),
        I256::from_i64(53i64),
        1,
        2,
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

        let (a_, b_) = matrix.wrapping_apply_to((a, b));
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
    fn test_conditional_swap() {
        let mut y = X.clone();
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
                1,
                2
            )
        );
    }

    #[test]
    fn test_conditional_subtract() {
        let mut y = X.clone();
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
                1,
                2
            )
        );
    }

    #[test]
    fn test_conditional_double() {
        let mut y = X.clone();
        y.conditional_double_bottom_row(ConstChoice::FALSE);
        assert_eq!(
            y,
            BinXgcdMatrix::new(
                Int::from(1i32),
                Int::from(7i32),
                Int::from(23i32),
                Int::from(53i32),
                1,
                3
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
                2,
                4
            )
        );
    }

    #[test]
    fn test_wrapping_mul() {
        let res = X.wrapping_mul_right(&X);
        assert_eq!(
            res,
            BinXgcdMatrix::new(
                I256::from_i64(162i64),
                I256::from_i64(378i64),
                I256::from_i64(1242i64),
                I256::from_i64(2970i64),
                2,
                4
            )
        )
    }
}
