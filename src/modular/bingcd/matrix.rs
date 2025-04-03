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
pub(crate) struct BinXgcdMatrix<const LIMBS: usize> {
    m00: Uint<LIMBS>,
    m01: Uint<LIMBS>,
    m10: Uint<LIMBS>,
    m11: Uint<LIMBS>,
    pattern: ConstChoice,
    k: u32,
    k_upper_bound: u32,
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

    pub(crate) const fn as_elements(
        &self,
    ) -> (
        &Uint<LIMBS>,
        &Uint<LIMBS>,
        &Uint<LIMBS>,
        &Uint<LIMBS>,
        ConstChoice,
        u32,
        u32,
    ) {
        (
            &self.m00,
            &self.m01,
            &self.m10,
            &self.m11,
            self.pattern,
            self.k,
            self.k_upper_bound,
        )
    }

    pub(crate) const fn as_elements_mut(
        &mut self,
    ) -> (
        &mut Uint<LIMBS>,
        &mut Uint<LIMBS>,
        &mut Uint<LIMBS>,
        &mut Uint<LIMBS>,
        &mut ConstChoice,
        &mut u32,
        &mut u32,
    ) {
        (
            &mut self.m00,
            &mut self.m01,
            &mut self.m10,
            &mut self.m11,
            &mut self.pattern,
            &mut self.k,
            &mut self.k_upper_bound,
        )
    }

    /// Return `b` if `c` is truthy, otherwise return `a`.
    #[inline]
    pub(crate) const fn select(a: &Self, b: &Self, c: ConstChoice) -> Self {
        Self {
            m00: Uint::select(&a.m00, &b.m00, c),
            m01: Uint::select(&a.m01, &b.m01, c),
            m10: Uint::select(&a.m10, &b.m10, c),
            m11: Uint::select(&a.m11, &b.m11, c),
            k: c.select_u32(a.k, b.k),
            k_upper_bound: c.select_u32(a.k_upper_bound, b.k_upper_bound),
            pattern: b.pattern.and(c).or(a.pattern.and(c.not())),
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
            m00a.wrapping_sub(&m01b)
                .div_2k(self.k)
                .wrapping_neg_if(self.pattern.not()),
            m11b.wrapping_sub(&m10a)
                .div_2k(self.k)
                .wrapping_neg_if(self.pattern.not()),
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
            self.pattern.eq(rhs.pattern),
            self.k + rhs.k,
            self.k_upper_bound + rhs.k_upper_bound,
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

    const X: BinXgcdMatrix<{ U256::LIMBS }> = BinXgcdMatrix::new(
        U256::from_u64(1u64),
        U256::from_u64(7u64),
        U256::from_u64(23u64),
        U256::from_u64(53u64),
        ConstChoice::TRUE,
        1,
        2,
    );

    #[test]
    fn test_wrapping_apply_to() {
        let a = U64::from_be_hex("CA048AFA63CD6A1F");
        let b = U64::from_be_hex("AE693BF7BE8E5566");
        let matrix = BinXgcdMatrix {
            m00: U64::from_be_hex("0000000000000120"),
            m01: U64::from_be_hex("00000000000000D0"),
            m10: U64::from_be_hex("0000000000000136"),
            m11: U64::from_be_hex("00000000000002A7"),
            pattern: ConstChoice::TRUE,
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
                Uint::from(23u32),
                Uint::from(53u32),
                Uint::from(1u32),
                Uint::from(7u32),
                ConstChoice::FALSE,
                1,
                2
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
                Uint::from(23u32),
                Uint::from(53u32),
                Uint::from(1u32),
                Uint::from(7u32),
                ConstChoice::FALSE,
                1,
                2
            )
        );
    }

    #[test]
    fn test_conditional_add_right_column_to_left() {
        let mut y = X;
        y.conditional_add_right_column_to_left(ConstChoice::FALSE);
        assert_eq!(y, X);
        y.conditional_add_right_column_to_left(ConstChoice::TRUE);
        assert_eq!(
            y,
            BinXgcdMatrix::new(
                Uint::from(6u32),
                Uint::from(7u32),
                Uint::from(30u32),
                Uint::from(53u32),
                ConstChoice::TRUE,
                1,
                2
            )
        );
    }

    #[test]
    fn test_conditional_subtract_bottom_row_from_top() {
        let mut y = X;
        y.conditional_subtract_bottom_row_from_top(ConstChoice::FALSE);
        assert_eq!(y, X);
        y.conditional_subtract_bottom_row_from_top(ConstChoice::TRUE);
        assert_eq!(
            y,
            BinXgcdMatrix::new(
                Uint::from(24u32),
                Uint::from(60u32),
                Uint::from(23u32),
                Uint::from(53u32),
                ConstChoice::TRUE,
                1,
                2
            )
        );
    }

    #[test]
    fn test_conditional_subtract_right_column_from_left() {
        let mut y = X;
        y.conditional_subtract_right_column_from_left(ConstChoice::FALSE);
        assert_eq!(y, X);
        y.conditional_subtract_right_column_from_left(ConstChoice::TRUE);
        assert_eq!(
            y,
            BinXgcdMatrix::new(
                Uint::from(8u32),
                Uint::from(7u32),
                Uint::from(76u32),
                Uint::from(53u32),
                ConstChoice::TRUE,
                1,
                2
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
                Uint::from(1u32),
                Uint::from(7u32),
                Uint::from(23u32),
                Uint::from(53u32),
                ConstChoice::TRUE,
                1,
                3
            )
        );
        y.conditional_double_bottom_row(ConstChoice::TRUE);
        assert_eq!(
            y,
            BinXgcdMatrix::new(
                Uint::from(1u32),
                Uint::from(7u32),
                Uint::from(46u32),
                Uint::from(106u32),
                ConstChoice::TRUE,
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
                U256::from(162u64),
                U256::from(378u64),
                U256::from(1242u64),
                U256::from(2970u64),
                ConstChoice::TRUE,
                2,
                4
            )
        )
    }

    #[test]
    fn test_select() {
        let x = BinXgcdMatrix::new(
            U64::from_u64(0),
            U64::from_u64(1),
            U64::from_u64(2),
            U64::from_u64(3),
            ConstChoice::FALSE,
            4,
            5,
        );
        let y = BinXgcdMatrix::new(
            U64::from_u64(6),
            U64::from_u64(7),
            U64::from_u64(8),
            U64::from_u64(9),
            ConstChoice::TRUE,
            11,
            12,
        );
        assert_eq!(BinXgcdMatrix::select(&x, &y, ConstChoice::FALSE), x);
        assert_eq!(BinXgcdMatrix::select(&x, &y, ConstChoice::TRUE), y);
    }
}
