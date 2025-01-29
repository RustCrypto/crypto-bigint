use crate::{ConcatMixed, ConstChoice, ConstCtOption, Int, Limb, Odd, Split, Uint, I64, U128};
use num_traits::{ToPrimitive, WrappingSub};

struct ExtendedInt<const LIMBS: usize, const EXTENSION_LIMBS: usize>(
    Uint<LIMBS>,
    Uint<EXTENSION_LIMBS>,
);

impl<const LIMBS: usize, const EXTRA: usize> ExtendedInt<LIMBS, EXTRA> {
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
        let shift_is_zero = ConstChoice::from_u32_eq(shift, 0);
        let left_shift = shift_is_zero.select_u32(Uint::<EXTRA>::BITS - shift, 0);

        let hi = self.1.shr(shift);
        // TODO: replace with carrying_shl
        let carry = Uint::select(&self.1, &Uint::ZERO, shift_is_zero).shl(left_shift);
        let mut lo = self.0.shr(shift);

        // Apply carry
        let limb_diff = LIMBS.wrapping_sub(EXTRA) as u32;
        let carry = carry.resize::<LIMBS>().shl_vartime(limb_diff * Limb::BITS);
        lo = lo.bitxor(&carry);

        Self(lo, hi)
    }

    pub const fn abs(&self) -> Self {
        let is_negative = self.1.as_int().is_negative();
        self.wrapping_neg_if(is_negative)
    }

    pub const fn unpack(&self) -> ConstCtOption<Uint<LIMBS>> {
        ConstCtOption::new(self.0, self.1.is_nonzero().not())
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

    #[inline]
    fn restricted_extended_gcd<const UPDATE_LIMBS: usize>(
        mut a: Uint<LIMBS>,
        mut b: Uint<LIMBS>,
        iterations: u32,
    ) -> (Matrix<Int<UPDATE_LIMBS>, 2>, u32) {
        debug_assert!(iterations < Uint::<UPDATE_LIMBS>::BITS);

        // Unit matrix
        let (mut f0, mut g0) = (Int::ONE, Int::ZERO);
        let (mut f1, mut g1) = (Int::ZERO, Int::ONE);

        // Compute the update matrix.
        let mut used_increments = 0;
        let mut j = 0;
        while j < iterations {
            j += 1;

            let a_odd = a.is_odd();
            let a_lt_b = Uint::lt(&a, &b);

            // swap if a odd and a < b
            let do_swap = a_odd.and(a_lt_b);
            Uint::conditional_swap(&mut a, &mut b, do_swap);
            Int::conditional_swap(&mut f0, &mut f1, do_swap);
            Int::conditional_swap(&mut g0, &mut g1, do_swap);

            // subtract a from b when a is odd
            a = Uint::select(&a, &a.wrapping_sub(&b), a_odd);
            f0 = Int::select(&f0, &f0.wrapping_sub(&f1), a_odd);
            g0 = Int::select(&g0, &g0.wrapping_sub(&g1), a_odd);

            // mul/div by 2 when b is non-zero.
            // Only apply operations when b ≠ 0, otherwise do nothing.
            let do_apply = b.is_nonzero();
            a = Uint::select(&a, &a.shr_vartime(1), do_apply);
            f1 = Int::select(&f1, &f1.shl_vartime(1), do_apply);
            g1 = Int::select(&g1, &g1.shl_vartime(1), do_apply);
            used_increments = do_apply.select_u32(used_increments, used_increments + 1);
        }

        (Matrix([[f0, f1], [g0, g1]]), used_increments)
    }

    pub fn new_gcd(&self, rhs: &Self) -> Self {
        let i = self.trailing_zeros();
        let j = rhs.trailing_zeros();
        let k = const_min(i, j);
        Self::new_odd_gcd(&self.shr(i), &rhs.shr(j).to_odd().unwrap()).shl(k)
    }

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
                .abs()
                .shr(used_increments)
                .unpack()
                .expect("top limb is zero");
            b = updated_b
                .abs()
                .shr(used_increments)
                .unpack()
                .expect("top limb is zero");
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
