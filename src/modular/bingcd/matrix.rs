use crate::modular::bingcd::extension::ExtendedInt;
use crate::{ConstChoice, Uint};

type Vector<T> = (T, T);

/// Matrix used to compute the Extended GCD using the Binary Extended GCD algorithm.
///
/// The internal state represents the matrix
/// ```text
///      true                       false
/// [  m00 -m01 ]               [ -m00  m01 ]
/// [ -m10  m11 ] / 2^k   or    [  m10 -m11 ] / 2^k
/// ```
/// depending on whether `pattern` is respectively truthy or not.
///
/// Since some of the operations conditionally increase `k`, this struct furthermore keeps track of
/// `k_upper_bound`; an upper bound on the value of `k`.
#[derive(Debug, Clone, Copy, PartialEq)]
pub(super) struct BinXgcdMatrix<const LIMBS: usize> {
    pub m00: Uint<LIMBS>,
    pub m01: Uint<LIMBS>,
    pub m10: Uint<LIMBS>,
    pub m11: Uint<LIMBS>,
    pub pattern: ConstChoice,
    pub k: u32,
    pub k_upper_bound: u32,
}

impl<const LIMBS: usize> BinXgcdMatrix<LIMBS> {
    /// The unit matrix.
    pub(crate) const UNIT: Self = Self::new(
        Uint::ONE,
        Uint::ZERO,
        Uint::ZERO,
        Uint::ONE,
        ConstChoice::TRUE,
        0,
        0,
    );

    pub(crate) const fn new(
        m00: Uint<LIMBS>,
        m01: Uint<LIMBS>,
        m10: Uint<LIMBS>,
        m11: Uint<LIMBS>,
        pattern: ConstChoice,
        k: u32,
        k_upper_bound: u32,
    ) -> Self {
        Self {
            m00,
            m01,
            m10,
            m11,
            pattern,
            k,
            k_upper_bound,
        }
    }

    /// Apply this matrix to a vector of [Uint]s, returning the result as a vector of
    /// [ExtendedInt]s.
    #[inline]
    pub(crate) const fn extended_apply_to<const VEC_LIMBS: usize, const UPPER_BOUND: u32>(
        &self,
        vec: Vector<Uint<VEC_LIMBS>>,
    ) -> Vector<ExtendedInt<VEC_LIMBS, LIMBS>> {
        let (a, b) = vec;
        let m00a = ExtendedInt::from_product(a, self.m00);
        let m10a = ExtendedInt::from_product(a, self.m10);
        let m01b = ExtendedInt::from_product(b, self.m01);
        let m11b = ExtendedInt::from_product(b, self.m11);
        (
            m00a.wrapping_sub(&m01b)
                .bounded_div_2k::<UPPER_BOUND>(self.k)
                .wrapping_neg_if(self.pattern.not()),
            m11b.wrapping_sub(&m10a)
                .bounded_div_2k::<UPPER_BOUND>(self.k)
                .wrapping_neg_if(self.pattern.not()),
        )
    }

    /// Apply this matrix to a vector of [Uint]s, returning the result as a vector of
    /// [ExtendedInt]s.
    #[inline]
    pub(crate) const fn extended_apply_to_vartime<const VEC_LIMBS: usize>(
        &self,
        vec: Vector<Uint<VEC_LIMBS>>,
    ) -> Vector<ExtendedInt<VEC_LIMBS, LIMBS>> {
        let (a, b) = vec;
        let m00a = ExtendedInt::from_product(a, self.m00);
        let m10a = ExtendedInt::from_product(a, self.m10);
        let m01b = ExtendedInt::from_product(b, self.m01);
        let m11b = ExtendedInt::from_product(b, self.m11);
        (
            m00a.wrapping_add(&m01b).div_2k_vartime(self.k),
            m11b.wrapping_add(&m10a).div_2k_vartime(self.k),
        )
    }

    /// Swap the rows of this matrix if `swap` is truthy. Otherwise, do nothing.
    #[inline]
    pub(crate) const fn conditional_swap_rows(&mut self, swap: ConstChoice) {
        Uint::conditional_swap(&mut self.m00, &mut self.m10, swap);
        Uint::conditional_swap(&mut self.m01, &mut self.m11, swap);
        self.pattern = self.pattern.xor(swap);
    }

    /// Swap the rows of this matrix.
    #[inline]
    pub(crate) const fn swap_rows(&mut self) {
        self.conditional_swap_rows(ConstChoice::TRUE);
    }

    /// Subtract the bottom row from the top if `subtract` is truthy. Otherwise, do nothing.
    #[inline]
    pub(crate) const fn conditional_subtract_bottom_row_from_top(&mut self, subtract: ConstChoice) {
        // Note: because the signs of the internal representation are stored in `pattern`,
        // subtracting one row from another involves _adding_ these rows instead.
        self.m00 = Uint::select(&self.m00, &self.m00.wrapping_add(&self.m10), subtract);
        self.m01 = Uint::select(&self.m01, &self.m01.wrapping_add(&self.m11), subtract);
    }

    /// Subtract the right column from the left if `subtract` is truthy. Otherwise, do nothing.
    #[inline]
    pub(crate) const fn conditional_subtract_right_column_from_left(
        &mut self,
        subtract: ConstChoice,
    ) {
        // Note: because the signs of the internal representation are stored in `pattern`,
        // subtracting one column from another involves _adding_ these columns instead.
        self.m00 = Uint::select(&self.m00, &self.m00.wrapping_add(&self.m01), subtract);
        self.m10 = Uint::select(&self.m10, &self.m10.wrapping_add(&self.m11), subtract);
    }

    /// If `add` is truthy, add the right column to the left. Otherwise, do nothing.
    #[inline]
    pub(crate) const fn conditional_add_right_column_to_left(&mut self, add: ConstChoice) {
        // Note: because the signs of the internal representation are stored in `pattern`,
        // subtracting one column from another involves _adding_ these columns instead.
        self.m00 = Uint::select(&self.m00, &self.m01.wrapping_sub(&self.m00), add);
        self.m10 = Uint::select(&self.m10, &self.m11.wrapping_sub(&self.m10), add);
    }

    /// Double the bottom row of this matrix if `double` is truthy. Otherwise, do nothing.
    #[inline]
    pub(crate) const fn conditional_double_bottom_row(&mut self, double: ConstChoice) {
        // safe to vartime; shr_vartime is variable in the value of shift only. Since this shift
        // is a public constant, the constant time property of this algorithm is not impacted.
        self.m10 = Uint::select(&self.m10, &self.m10.shl_vartime(1), double);
        self.m11 = Uint::select(&self.m11, &self.m11.shl_vartime(1), double);
        self.k = double.select_u32(self.k, self.k + 1);
        self.k_upper_bound += 1;
    }

    /// Negate the elements in this matrix if `negate` is truthy. Otherwise, do nothing.
    #[inline]
    pub(crate) const fn conditional_negate(&mut self, negate: ConstChoice) {
        self.pattern = self.pattern.xor(negate);
    }
}

#[cfg(test)]
mod tests {
    use crate::modular::bingcd::matrix::BinXgcdMatrix;
    use crate::{ConstChoice, U64, U256, Uint};

    impl<const LIMBS: usize> BinXgcdMatrix<LIMBS> {
        pub(crate) const fn new_u64(
            matrix: (u64, u64, u64, u64),
            pattern: ConstChoice,
            k: u32,
            k_upper_bound: u32,
        ) -> Self {
            Self {
                m00: Uint::from_u64(matrix.0),
                m01: Uint::from_u64(matrix.1),
                m10: Uint::from_u64(matrix.2),
                m11: Uint::from_u64(matrix.3),
                pattern,
                k,
                k_upper_bound,
            }
        }
    }

    const X: BinXgcdMatrix<{ U256::LIMBS }> =
        BinXgcdMatrix::new_u64((1u64, 7u64, 23u64, 53u64), ConstChoice::TRUE, 6, 8);

    #[test]
    fn test_wrapping_apply_to() {
        let a = U64::from_be_hex("CA048AFA63CD6A1F");
        let b = U64::from_be_hex("AE693BF7BE8E5566");
        let matrix = BinXgcdMatrix::<{ U64::LIMBS }>::new_u64(
            (288, 208, 310, 679),
            ConstChoice::TRUE,
            17,
            17,
        );

        let (a_, b_) = matrix.extended_apply_to::<{ U64::LIMBS }, 18>((a, b));
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
        let target = BinXgcdMatrix::new_u64((23, 53, 1, 7), ConstChoice::FALSE, 6, 8);
        assert_eq!(y, target);
    }

    #[test]
    fn test_conditional_swap() {
        let mut y = X;
        y.conditional_swap_rows(ConstChoice::FALSE);
        assert_eq!(y, X);
        y.conditional_swap_rows(ConstChoice::TRUE);
        let target = BinXgcdMatrix::new_u64((23, 53, 1, 7), ConstChoice::FALSE, 6, 8);
        assert_eq!(y, target);
    }

    #[test]
    fn test_conditional_add_right_column_to_left() {
        let mut y = X;
        y.conditional_add_right_column_to_left(ConstChoice::FALSE);
        assert_eq!(y, X);
        y.conditional_add_right_column_to_left(ConstChoice::TRUE);

        let target = BinXgcdMatrix::new_u64((6u64, 7u64, 30u64, 53u64), ConstChoice::TRUE, 6, 8);
        assert_eq!(y, target);
    }

    #[test]
    fn test_conditional_subtract_bottom_row_from_top() {
        let mut y = X;
        y.conditional_subtract_bottom_row_from_top(ConstChoice::FALSE);
        assert_eq!(y, X);
        y.conditional_subtract_bottom_row_from_top(ConstChoice::TRUE);
        let target = BinXgcdMatrix::new_u64((24u64, 60u64, 23u64, 53u64), ConstChoice::TRUE, 6, 8);
        assert_eq!(y, target);
    }

    #[test]
    fn test_conditional_subtract_right_column_from_left() {
        let mut y = X;
        y.conditional_subtract_right_column_from_left(ConstChoice::FALSE);
        assert_eq!(y, X);
        y.conditional_subtract_right_column_from_left(ConstChoice::TRUE);
        let target = BinXgcdMatrix::new_u64((8u64, 7u64, 76u64, 53u64), ConstChoice::TRUE, 6, 8);
        assert_eq!(y, target);
    }

    #[test]
    fn test_conditional_double() {
        let mut y = X;
        y.conditional_double_bottom_row(ConstChoice::FALSE);
        let target = BinXgcdMatrix::new_u64((1u64, 7u64, 23u64, 53u64), ConstChoice::TRUE, 6, 9);
        assert_eq!(y, target);
        y.conditional_double_bottom_row(ConstChoice::TRUE);
        let target = BinXgcdMatrix::new_u64((1u64, 7u64, 46u64, 106u64), ConstChoice::TRUE, 7, 10);
        assert_eq!(y, target);
    }
}
