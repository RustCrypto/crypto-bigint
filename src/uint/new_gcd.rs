use crate::{ConstChoice, ConstCtOption, Int, Limb, Odd, Uint, I64, U128};
use num_traits::WrappingSub;

struct ExtendedInt<const LIMBS: usize, const EXTENSION_LIMBS: usize>(
    Uint<LIMBS>,
    Uint<EXTENSION_LIMBS>,
);

impl<const LIMBS: usize, const EXTRA: usize> ExtendedInt<LIMBS, EXTRA> {

    const ZERO: ExtendedInt<LIMBS, EXTRA> = Self(Uint::ZERO, Uint::ZERO);

    /// Construct an [ExtendedInt] from the product of a [Uint<LIMBS>] and an [Int<EXTRA>].
    pub const fn from_product(lhs: Uint<LIMBS>, rhs: Int<EXTRA>) -> Self {
        let (lo, hi, sgn) = rhs.split_mul_uint_right(&lhs);
        ExtendedInt(lo, hi).wrapping_neg_if(sgn)
    }

    pub const fn wrapping_neg(&self) -> Self {
        let (lhs, carry) = self.0.carrying_neg();
        let mut rhs = self.1.not();
        rhs = Uint::select(&rhs, &rhs.wrapping_add(&Uint::ONE), carry);
        Self(lhs, rhs)
    }

    pub const fn wrapping_neg_if(&self, negate: ConstChoice) -> Self {
        let neg = self.wrapping_neg();
        Self(
            Uint::select(&self.0, &neg.0, negate),
            Uint::select(&self.1, &neg.1, negate),
        )
    }

    pub const fn wrapping_add(&self, rhs: &Self) -> Self {
        let (lo, carry) = self.0.adc(&rhs.0, Limb::ZERO);
        let (hi, _) = self.1.adc(&rhs.1, carry);
        Self(lo, hi)
    }

    pub const fn shr(&self, shift: u32) -> Self {
        debug_assert!(shift <= Uint::<EXTRA>::BITS);

        let shift_is_zero = ConstChoice::from_u32_eq(shift, 0);
        let left_shift = shift_is_zero.select_u32(Uint::<EXTRA>::BITS - shift, 0);

        let hi = *self.1.as_int().shr(shift).as_uint();
        // TODO: replace with carrying_shl
        let carry = Uint::select(&self.1, &Uint::ZERO, shift_is_zero).shl(left_shift);
        let mut lo = self.0.shr(shift);

        // Apply carry
        let limb_diff = LIMBS.wrapping_sub(EXTRA) as u32;
        let carry = carry.resize::<LIMBS>().shl_vartime(limb_diff * Limb::BITS);
        lo = lo.bitxor(&carry);

        Self(lo, hi)
    }

    pub const fn unpack(&self) -> ConstCtOption<Int<LIMBS>> {
        let lo_is_negative = self.0.as_int().is_negative();
        let proper_positive = Int::eq(&self.1.as_int(), &Int::ZERO).and(lo_is_negative.not());
        let proper_negative = Int::eq(&self.1.as_int(), &Int::MINUS_ONE).and(lo_is_negative);
        ConstCtOption::new(self.0.as_int(), proper_negative.or(proper_positive))
    }

    /// Return `b` if `c` is truthy, otherwise return `a`.
    pub const fn select(a: &Self, b: &Self, c: ConstChoice) -> Self {
        Self(Uint::select(&a.0, &b.0, c), Uint::select(&a.1, &b.1, c))
    }

    /// Divide self by `2^k`.
    pub const fn div_2k(&self, k: u32) -> Self {
        let lo_is_minus_one = Int::eq(&self.0.as_int(), &Int::MINUS_ONE);
        let ext_is_minus_one = Int::eq(&self.1.as_int(), &Int::MINUS_ONE);
        Self::select(&self.shr(k), &Self::ZERO, lo_is_minus_one.and(ext_is_minus_one))
    }
}

struct Matrix<T, const DIM: usize>([[T; DIM]; DIM]);
impl<const LIMBS: usize> Matrix<Int<LIMBS>, 2> {

    #[inline]
    const fn extended_apply_to<const VEC_LIMBS: usize>(
        &self,
        vec: (Uint<VEC_LIMBS>, Uint<VEC_LIMBS>),
    ) -> (ExtendedInt<VEC_LIMBS, LIMBS>, ExtendedInt<VEC_LIMBS, LIMBS>) {
        let (a, b) = vec;
        let a00 = ExtendedInt::from_product(a, self.0[0][0]);
        let a01 = ExtendedInt::from_product(a, self.0[0][1]);
        let b10 = ExtendedInt::from_product(b, self.0[1][0]);
        let b11 = ExtendedInt::from_product(b, self.0[1][1]);
        (a00.wrapping_add(&b10), a01.wrapping_add(&b11))
    }
}

/// `const` equivalent of `u32::max(a, b)`.
const fn const_max(a: u32, b: u32) -> u32 {
    ConstChoice::from_u32_lt(a, b).select_u32(a, b)
}

/// `const` equivalent of `u32::min(a, b)`.
const fn const_min(a: u32, b: u32) -> u32 {
    ConstChoice::from_u32_lt(a, b).select_u32(b, a)
}

impl<const LIMBS: usize> Uint<LIMBS> {
    /// Construct a [Uint] containing the bits in `self` in the range `[idx, idx + length)`.
    ///
    /// Assumes `length ≤ Uint::<SECTION_LIMBS>::BITS` and `idx + length ≤ Self::BITS`.
    #[inline(always)]
    const fn section<const SECTION_LIMBS: usize>(
        &self,
        idx: u32,
        length: u32,
    ) -> Uint<SECTION_LIMBS> {
        debug_assert!(length <= Uint::<SECTION_LIMBS>::BITS);
        debug_assert!(idx + length <= Self::BITS);

        let mask = Uint::ONE.shl(length).wrapping_sub(&Uint::ONE);
        self.shr(idx).resize::<SECTION_LIMBS>().bitand(&mask)
    }

    /// Construct a [Uint] containing the bits in `self` in the range `[idx, idx + length)`.
    ///
    /// Assumes `length ≤ Uint::<SECTION_LIMBS>::BITS` and `idx + length ≤ Self::BITS`.
    ///
    /// Executes in time variable in `idx` only.
    #[inline(always)]
    const fn section_vartime<const SECTION_LIMBS: usize>(
        &self,
        idx: u32,
        length: u32,
    ) -> Uint<SECTION_LIMBS> {
        debug_assert!(length <= Uint::<SECTION_LIMBS>::BITS);
        debug_assert!(idx + length <= Self::BITS);

        let mask = Uint::ONE.shl_vartime(length).wrapping_sub(&Uint::ONE);
        self.shr_vartime(idx)
            .resize::<SECTION_LIMBS>()
            .bitand(&mask)
    }

    /// Compact `self` to a form containing the concatenation of its bit ranges `[0, k-1)`
    /// and `[n-k-1, n)`.
    ///
    /// Assumes `k ≤ Uint::<SUMMARY_LIMBS>::BITS`, `n ≤ Self::BITS` and `n ≥ 2k`.
    #[inline(always)]
    const fn compact<const SUMMARY_LIMBS: usize>(&self, n: u32, k: u32) -> Uint<SUMMARY_LIMBS> {
        debug_assert!(k <= Uint::<SUMMARY_LIMBS>::BITS);
        debug_assert!(n <= Self::BITS);
        debug_assert!(n >= 2 * k);

        let hi = self.section(n - k - 1, k + 1);
        let lo = self.section_vartime(0, k - 1);
        hi.shl_vartime(k - 1).bitxor(&lo)
    }

    /// Constructs a matrix `M` s.t. for `(A, B) = M(a,b)` it holds that  
    /// - `gcd(A, B) = gcd(a, b)`, and
    /// - `A.bits() < a.bits()` and/or `B.bits() < b.bits()`.
    /// 
    /// Moreover, it returns `log_upper_bound: u32` s.t. each element in `M` lies in the interval
    /// `(-2^log_upper_bound, 2^log_upper_bound]`.
    ///
    /// Assumes `iterations < Uint::<UPDATE_LIMBS>::BITS / 2`.
    #[inline]
    fn restricted_extended_gcd<const UPDATE_LIMBS: usize>(
        mut a: Uint<LIMBS>,
        mut b: Uint<LIMBS>,
        iterations: u32,
    ) -> (Matrix<Int<UPDATE_LIMBS>, 2>, u32) {
        debug_assert!(iterations < Uint::<UPDATE_LIMBS>::BITS / 2);

        // Unit matrix
        let (mut f00, mut f01) = (Int::ONE, Int::ZERO);
        let (mut f10, mut f11) = (Int::ZERO, Int::ONE);

        // Compute the update matrix.
        let mut log_upper_bound = 0;
        let mut j = 0;
        while j < iterations {
            j += 1;

            let a_odd = a.is_odd();
            let a_lt_b = Uint::lt(&a, &b);

            // swap if a odd and a < b
            let do_swap = a_odd.and(a_lt_b);
            Uint::conditional_swap(&mut a, &mut b, do_swap);
            Int::conditional_swap(&mut f00, &mut f10, do_swap);
            Int::conditional_swap(&mut f01, &mut f11, do_swap);

            // subtract a from b when a is odd
            a = Uint::select(&a, &a.wrapping_sub(&b), a_odd);
            f00 = Int::select(&f00, &f00.wrapping_sub(&f10), a_odd);
            f01 = Int::select(&f01, &f01.wrapping_sub(&f11), a_odd);

            // mul/div by 2 when b is non-zero.
            // Only apply operations when b ≠ 0, otherwise do nothing.
            let do_apply = b.is_nonzero();
            a = Uint::select(&a, &a.shr_vartime(1), do_apply);
            f10 = Int::select(&f10, &f10.shl_vartime(1), do_apply);
            f11 = Int::select(&f11, &f11.shl_vartime(1), do_apply);
            log_upper_bound = do_apply.select_u32(log_upper_bound, log_upper_bound + 1);
        }

        (Matrix([[f00, f10], [f01, f11]]), log_upper_bound)
    }

    /// Compute the greatest common divisor of `self` and `rhs`.
    pub fn new_gcd(&self, rhs: &Self) -> Self {
        // Leverage two GCD identity rules to make self and rhs odd.
        // 1) gcd(2a, 2b) = 2 * gcd(a, b)
        // 2) gcd(a, 2b) = gcd(a, b) if a is odd.
        let i = self.trailing_zeros();
        let j = rhs.trailing_zeros();
        let k = const_min(i, j);
        Self::new_odd_gcd(&self.shr(i), &rhs.shr(j).to_odd().unwrap()).shl(k)
    }

    /// Compute the greatest common divisor of `self` and `rhs`.
    pub fn new_odd_gcd(&self, rhs: &Odd<Self>) -> Self {
        /// Window size.
        const K: u32 = 63;
        /// Smallest [Int] that fits a K-bit [Uint].
        type SingleK = I64;
        /// Smallest [Uint] that fits 2K bits.
        type DoubleK = U128;
        debug_assert!(DoubleK::BITS >= 2 * K);

        let (mut a, mut b) = (*self, rhs.get());

        let mut i = 0;
        while i < (2 * Self::BITS - 1).div_ceil(K) {
            i += 1;

            // Construct a_ and b_ as the summary of a and b, respectively.
            let n = const_max(2 * K, const_max(a.bits(), b.bits()));
            let a_: DoubleK = a.compact(n, K);
            let b_: DoubleK = b.compact(n, K);

            // Compute the K-1 iteration update matrix from a_ and b_
            let (matrix, used_increments) =
                Uint::restricted_extended_gcd::<{ SingleK::LIMBS }>(a_, b_, K - 1);

            // Update `a` and `b` using the update matrix
            let (updated_a, updated_b) = matrix.extended_apply_to((a, b));

            a = updated_a
                .div_2k(used_increments)
                .unpack()
                .expect("top limb is zero")
                .abs();
            b = updated_b
                .div_2k(used_increments)
                .unpack()
                .expect("top limb is zero")
                .abs();
        }

        b
    }
}

#[cfg(test)]
mod tests {
    use crate::{ConcatMixed, Gcd, Random, Split, Uint, U2048};
    use rand_core::OsRng;

    fn gcd_comparison_test<const LIMBS: usize, const DOUBLE: usize>(
        lhs: Uint<LIMBS>,
        rhs: Uint<LIMBS>,
    ) where
        Uint<LIMBS>: Gcd<Output = Uint<LIMBS>>,
        Uint<LIMBS>: ConcatMixed<Uint<LIMBS>, MixedOutput = Uint<DOUBLE>>,
        Uint<DOUBLE>: Split,
    {
        let gcd = lhs.gcd(&rhs);
        let bingcd = lhs.new_odd_gcd(&rhs.to_odd().unwrap());
        assert_eq!(gcd, bingcd);
    }

    #[test]
    fn test_new_gcd() {
        for _ in 0..500 {
            let x = U2048::random(&mut OsRng);
            let mut y = U2048::random(&mut OsRng);

            y = Uint::select(&(y.wrapping_add(&Uint::ONE)), &y, y.is_odd());

            gcd_comparison_test(x, y);
        }
    }
}
