use crate::{
    ConcatMixed, ConstChoice, ConstCtOption, Int, Limb, Odd, Split, Uint,
    I64, U64,
};
use core::cmp::min;
use num_traits::WrappingSub;

struct UintPlus<const LIMBS: usize>(Uint<LIMBS>, Limb);

impl<const LIMBS: usize> UintPlus<LIMBS> {
    pub const fn wrapping_neg(&self) -> Self {
        let (lhs, carry) = self.0.carrying_neg();
        let mut rhs = self.1.not();
        rhs = Limb::select(rhs, rhs.wrapping_add(Limb::ONE), carry);
        Self(lhs, rhs)
    }

    pub const fn wrapping_neg_if(&self, negate: ConstChoice) -> Self {
        let neg = self.wrapping_neg();
        Self(
            Uint::select(&self.0, &neg.0, negate),
            Limb::select(self.1, neg.1, negate),
        )
    }

    pub const fn wrapping_add(&self, rhs: &Self) -> Self {
        let (lo, carry) = self.0.adc(&rhs.0, Limb::ZERO);
        let (hi, _) = self.1.adc(rhs.1, carry);
        Self(lo, hi)
    }

    pub const fn shr(&self, shift: u32) -> Self {
        let hi = self.1.shr(shift);
        let zero_shift = ConstChoice::from_u32_eq(shift, 0);
        let leftshift = zero_shift.select_u32(Limb::BITS - shift, 0);
        let carry = Limb::select(self.1.shl(leftshift), Limb::ZERO, zero_shift);
        let mut lo = self.0.shr(shift);
        lo.as_limbs_mut()[LIMBS - 1] = lo.as_limbs_mut()[LIMBS - 1].bitxor(carry);
        Self(lo, hi)
    }

    pub const fn abs(&self) -> Self {
        let is_negative = ConstChoice::from_word_msb(self.1.bitand(Limb::ONE.shl(Limb::HI_BIT)).0);
        self.wrapping_neg_if(is_negative)
    }

    pub const fn unpack(&self) -> ConstCtOption<Uint<LIMBS>> {
        ConstCtOption::new(self.0, self.1.is_nonzero().not())
    }
}

type UpdateMatrix<const LIMBS: usize> = (Int<LIMBS>, Int<LIMBS>, Int<LIMBS>, Int<LIMBS>);

/// `const` equivalent of `u32::max(a, b)`.
const fn const_max(a: u32, b: u32) -> u32 {
    ConstChoice::from_u32_lt(a, b).select_u32(a, b)
}

/// `const` equivalent of `u32::min(a, b)`.
const fn const_min(a: u32, b: u32) -> u32 {
    ConstChoice::from_u32_lt(a, b).select_u32(b, a)
}

impl<const LIMBS: usize> Uint<LIMBS> {

    #[inline]
    fn cutdown<const K: u32, const CUTDOWN_LIMBS: usize>(
        a: Self,
        b: Self,
    ) -> (Uint<CUTDOWN_LIMBS>, Uint<CUTDOWN_LIMBS>) {
        let k_sub_one_bitmask = Uint::<CUTDOWN_LIMBS>::ONE
            .shl_vartime(K - 1)
            .wrapping_sub(&Uint::<CUTDOWN_LIMBS>::ONE);

        // Construct a_ and b_ as the concatenation of the K most significant and the K least
        // significant bits of a and b, respectively. If those bits overlap, ... TODO
        let n = const_max(2 * K, const_max(a.bits(), b.bits()));

        let hi_a = a.shr(n - K - 1).resize::<{ CUTDOWN_LIMBS }>(); // top k+1 bits
        let lo_a = a.resize::<CUTDOWN_LIMBS>().bitand(&k_sub_one_bitmask); // bottom k-1 bits
        let a_ = hi_a.shl_vartime(K - 1).bitxor(&lo_a);

        let hi_b = b.shr(n - K - 1).resize::<CUTDOWN_LIMBS>();
        let lo_b = b.resize::<CUTDOWN_LIMBS>().bitand(&k_sub_one_bitmask);
        let b_ = hi_b.shl_vartime(K - 1).bitxor(&lo_b);

        (a_, b_)
    }

    #[inline]
    fn restricted_extended_gcd<const UPDATE_LIMBS: usize>(
        mut a: Uint<LIMBS>,
        mut b: Uint<LIMBS>,
        iterations: u32,
    ) -> (UpdateMatrix<UPDATE_LIMBS>, u32) {
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

        ((f0, f1, g0, g1), used_increments)
    }

    pub fn new_gcd(&self, rhs: &Self) -> Self {
        let i = self.trailing_zeros();
        let j = rhs.trailing_zeros();
        let k = const_min(i, j);
        Self::new_odd_gcd(&self.shr(i), &rhs.shr(j).to_odd().unwrap()).shl(k)
    }

    pub fn new_odd_gcd(&self, rhs: &Odd<Self>) -> Self {
        /// Window size.
        const K: u32 = 32;
        /// Smallest [Int] that fits a K-bit [Uint].
        type SingleK = I64;
        /// Smallest [Uint] that fits 2K bits.
        type DoubleK = U64;
        debug_assert!(DoubleK::BITS >= 2 * K);

        let (mut a, mut b) = (*self, rhs.get());

        let mut i = 0;
        while i < (2 * rhs.bits_vartime() - 1).div_ceil(K) {
            i += 1;

            let (a_, b_) = Self::cutdown::<K, { DoubleK::LIMBS }>(a, b);


            // Compute the K-1 iteration update matrix from a_ and b_
            let (matrix, used_increments) =
                Uint::restricted_extended_gcd::<{ SingleK::LIMBS }>(a_, b_, K - 1);
            let (f0, f1, g0, g1) = matrix;

            // Pack together into one object
            let (lo_af0, hi_af0, sgn_af0) = f0.split_mul_uint_right(&a);
            let (lo_bg0, hi_bg0, sgn_bg0) = g0.split_mul_uint_right(&b);
            let af0 = UintPlus(lo_af0, hi_af0.as_limbs()[0]).wrapping_neg_if(sgn_af0);
            let bg0 = UintPlus(lo_bg0, hi_bg0.as_limbs()[0]).wrapping_neg_if(sgn_bg0);

            // Pack together into one object
            let (lo_af1, hi_af1, sgn_af1) = f1.split_mul_uint_right(&a);
            let (lo_bg1, hi_bg1, sgn_bg1) = g1.split_mul_uint_right(&b);
            let af1 = UintPlus(lo_af1, hi_af1.as_limbs()[0]).wrapping_neg_if(sgn_af1);
            let bg1 = UintPlus(lo_bg1, hi_bg1.as_limbs()[0]).wrapping_neg_if(sgn_bg1);

            a = af0
                .wrapping_add(&bg0)
                .abs()
                .shr(used_increments)
                .unpack()
                .expect("top limb is zero");
            b = af1
                .wrapping_add(&bg1)
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
