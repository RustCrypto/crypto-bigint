use core::cmp::min;
use num_traits::WrappingSub;
use subtle::Choice;
use crate::{ConstChoice, Int, Limb, Uint, Word, I64, U64, CheckedSub, CheckedMul, ConcatMixed, Split, Odd};

impl<const LIMBS: usize> Uint<LIMBS> {
    /// Given `a, b, f` and `g`, compute `(a*f + b*g) / 2^{k-1}`, where it is given that
    /// `f.bits()` and `g.bits() <= 2^{k-1}`
    #[inline(always)]
    const fn addmul_shr_k_sub_1<const K: u32, const RHS_LIMBS: usize>(
        a: Uint<{ LIMBS }>,
        b: Uint<{ LIMBS }>,
        f: I64,
        g: I64,
    ) -> Int<{ LIMBS }> {
        let k_sub_one_bitmask: U64 = U64::ONE.shl_vartime(K - 1).wrapping_sub(&U64::ONE);
        // mul
        let (mut lo_af0, mut hi_af0, sgn_af0) = f.split_mul_uint(&a);
        let (mut lo_bg0, mut hi_bg0, sgn_bg0) = g.split_mul_uint(&b);
        // negate if required
        lo_af0 = lo_af0.wrapping_neg_if(sgn_af0);
        lo_bg0 = lo_bg0.wrapping_neg_if(sgn_bg0);
        hi_af0 = Uint::select(
            &hi_af0,
            &(hi_af0
                .not()
                .adc(
                    &Uint::ZERO,
                    Limb::select(
                        Limb::ZERO,
                        Limb::ONE,
                        sgn_af0.and(lo_af0.is_nonzero().not()),
                    ),
                )
                .0),
            sgn_af0,
        );
        hi_bg0 = Uint::select(
            &hi_bg0,
            &(hi_bg0
                .not()
                .adc(
                    &Uint::ZERO,
                    Limb::select(
                        Limb::ZERO,
                        Limb::ONE,
                        sgn_bg0.and(lo_bg0.is_nonzero().not()),
                    ),
                )
                .0),
            sgn_bg0,
        );
        // sum
        let (lo_sum, carry) = lo_af0.as_int().overflowing_add(&lo_bg0.as_int());
        let mut hi_sum = hi_af0.as_int().checked_add(&hi_bg0.as_int()).expect("TODO");
        // deal with carry
        hi_sum = Int::select(&hi_sum, &hi_sum.wrapping_add(&Int::ONE), carry);
        // div by 2^{k-1}
        let shifted_lo_sum = lo_sum
            .as_uint()
            .shr_vartime(K - 1)
            .bitand(&k_sub_one_bitmask);
        let mut shifted_hi_sum = hi_sum.shl_vartime(I64::BITS - K + 1);
        // Note: we're assuming K-1 <= Word::BITS here.
        debug_assert!(K - 1 <= Word::BITS);
        shifted_hi_sum.as_limbs_mut()[0] = shifted_hi_sum.as_limbs_mut()[0].bitxor(shifted_lo_sum.as_limbs()[0]);
        shifted_hi_sum
    }

    const fn const_max(a: u32, b: u32) -> u32 {
        ConstChoice::from_u32_lt(a, b).select_u32(a, b)
    }

    pub fn new_gcd(mut a: Self, mut b: Self) -> Self {
        // Using identities 2 and 3:
        // gcd(2ⁱ u, 2ʲ v) = 2ᵏ gcd(u, v) with u, v odd and k = min(i, j)
        // 2ᵏ is the greatest power of two that divides both 2ⁱ u and 2ʲ v
        let i = a.trailing_zeros(); a = a.shr(i);
        let j = b.trailing_zeros(); b = b.shr(j);
        let k = min(i, j);

        // Note: at this point both elements are odd.
        Self::new_odd_gcd(a, b).shl(k)
    }

    pub fn new_odd_gcd(mut a: Self, mut b: Self) -> Self {
        let mut i = 0;
        while i < 2 * Self::BITS {
            // Swap s.t. a ≤ b
            let do_swap = Uint::gt(&a, &b);
            Uint::conditional_swap(&mut a, &mut b, do_swap);

            // Identity 4: gcd(a, b) = gcd(a, b-a)
            b -= a;

            // Identity 3: gcd(a, 2ʲ b) = gcd(a, b) as a is odd
            let do_shift = a.is_nonzero().and(b.is_nonzero());
            let shift = do_shift.select_u32(0, b.trailing_zeros());
            b = b.shr(shift);

            i += 1;
        }

        b
    }

    #[inline]
    fn cutdown<const K: u32, const CUTDOWN_LIMBS: usize>(a: Self, b: Self) -> (Uint<CUTDOWN_LIMBS>, Uint<CUTDOWN_LIMBS>) {
        let k_sub_one_bitmask = Uint::<CUTDOWN_LIMBS>::ONE.shl_vartime(K-1).wrapping_sub(&Uint::<CUTDOWN_LIMBS>::ONE);

        // Construct a_ and b_ as the concatenation of the K most significant and the K least
        // significant bits of a and b, respectively. If those bits overlap, ... TODO
        let n = Self::const_max(2 * K, Self::const_max(a.bits(), b.bits()));

        let hi_a = a.shr(n - K - 1).resize::<{ CUTDOWN_LIMBS }>(); // top k+1 bits
        let lo_a = a.resize::<CUTDOWN_LIMBS>().bitand(&k_sub_one_bitmask); // bottom k-1 bits
        let mut a_ = hi_a.shl_vartime(K - 1).bitxor(&lo_a);

        let hi_b = b.shr(n - K - 1).resize::<CUTDOWN_LIMBS>();
        let lo_b = b.resize::<CUTDOWN_LIMBS>().bitand(&k_sub_one_bitmask);
        let mut b_ = hi_b.shl_vartime(K - 1).bitxor(&lo_b);

        (a_, b_)
    }

    pub fn new_gcd_<const DOUBLE: usize>(&self, rhs: &Self) -> Self
    where
        Uint<LIMBS>: ConcatMixed<Uint<LIMBS>, MixedOutput=Uint<DOUBLE>>,
        Uint<DOUBLE>: Split,
    {
        let i = self.trailing_zeros();
        let j = rhs.trailing_zeros();
        let k = min(i, j);
        Self::new_gcd_odd(&self.shr(i), &rhs.shr(j).to_odd().unwrap()).shl(k)
    }

    pub fn new_gcd_odd<const DOUBLE: usize>(&self, rhs: &Odd<Self>) -> Self
    where
        Uint<LIMBS>: ConcatMixed<Uint<LIMBS>, MixedOutput=Uint<DOUBLE>>,
        Uint<DOUBLE>: Split,
    {
        /// Window size.
        const K: u32 = 32;
        /// Smallest [Uint] that fits K bits
        type SingleK = I64;
        /// Smallest [Uint] that fits 2K bits.
        type DoubleK = U64;
        debug_assert!(DoubleK::BITS >= 2 * K);
        const K_SUB_ONE_BITMASK: DoubleK =
            DoubleK::ONE.shl_vartime(K - 1).wrapping_sub(&DoubleK::ONE);

        let (mut a, mut b) = (*self, rhs.get());

        let mut i = 0;
        while i < (2 * rhs.bits_vartime() - 1).div_ceil(K) {
            i += 1;

            let (mut a_, mut b_) = Self::cutdown::<K, {DoubleK::LIMBS}>(a, b);

            // Unit matrix
            let (mut f0, mut g0) = (SingleK::ONE, SingleK::ZERO);
            let (mut f1, mut g1) = (SingleK::ZERO, SingleK::ONE);

            // Compute the update matrix.
            let mut used_increments = 0;
            let mut j = 0;
            while j < K - 1 {
                j += 1;

                let a_odd = a_.is_odd();
                let a_lt_b = DoubleK::lt(&a_, &b_);

                // swap if a odd and a < b
                let do_swap = a_odd.and(a_lt_b);
                DoubleK::conditional_swap(&mut a_, &mut b_, do_swap);
                SingleK::conditional_swap(&mut f0, &mut f1, do_swap);
                SingleK::conditional_swap(&mut g0, &mut g1, do_swap);

                // subtract a from b when a is odd and b is non-zero
                a_ = DoubleK::select(&a_, &a_.wrapping_sub(&b_), a_odd);
                f0 = SingleK::select(&f0, &f0.wrapping_sub(&f1), a_odd);
                g0 = SingleK::select(&g0, &g0.wrapping_sub(&g1), a_odd);

                // mul/div by 2 when b is non-zero.
                // Only apply operations when b ≠ 0, otherwise do nothing.
                let do_apply = b_.is_nonzero();
                a_ = DoubleK::select(&a_, &a_.shr_vartime(1), do_apply);
                f1 = SingleK::select(&f1, &f1.shl_vartime(1), do_apply);
                g1 = SingleK::select(&g1, &g1.shl_vartime(1), do_apply);
                used_increments = do_apply.select_u32(used_increments, used_increments + 1);
            }

            // TODO: fix this
            let mut f0 = f0.resize::<LIMBS>();
            let mut f1 = f1.resize::<LIMBS>();
            let mut g0 = g0.resize::<LIMBS>();
            let mut g1 = g1.resize::<LIMBS>();

            let (new_a, new_b) = (
                f0.widening_mul_uint(&a).wrapping_add(&g0.widening_mul_uint(&b)).shr(used_increments),
                f1.widening_mul_uint(&a).wrapping_add(&g1.widening_mul_uint(&b)).shr(used_increments)
            );

            a = new_a.resize::<LIMBS>().abs();
            b = new_b.resize::<LIMBS>().abs();
        }

        b
    }
}

#[cfg(test)]
mod tests {
    use crate::{Uint, Random, U2048, Gcd, ConcatMixed, Split};
    use rand_core::OsRng;

    fn gcd_comparison_test<const LIMBS: usize, const DOUBLE: usize>(lhs: Uint<LIMBS>, rhs: Uint<LIMBS>)
    where
        Uint<LIMBS>: Gcd<Output=Uint<LIMBS>>,
        Uint<LIMBS>: ConcatMixed<Uint<LIMBS>, MixedOutput=Uint<DOUBLE>>,
        Uint<DOUBLE>: Split
    {
        let gcd = lhs.gcd(&rhs);
        let new_gcd = Uint::new_gcd(lhs, rhs);
        let bingcd = lhs.new_gcd_odd(&rhs.to_odd().unwrap());

        assert_eq!(gcd, new_gcd);
        assert_eq!(gcd, bingcd);
    }

    #[test]
    fn test_new_gcd() {
        for _ in 0..500 {
            let x = U2048::random(&mut OsRng);
            let mut y = U2048::random(&mut OsRng);

            y = Uint::select(&(y.wrapping_add(&Uint::ONE)), &y, y.is_odd());

            gcd_comparison_test(x,y);
        }
    }
}
