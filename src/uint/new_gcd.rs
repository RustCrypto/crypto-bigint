use crate::{ConstChoice, Int, Limb, Uint, Word, I64, U64, CheckedSub, CheckedMul};

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

    pub fn new_xgcd_odd_vartime(&self, rhs: &Self) -> (Self, Self, Int<LIMBS>, Int<LIMBS>) {
        /// Window size.
        const K: u32 = 32;
        /// Smallest [Uint] that fits K bits
        type SingleK = I64;
        /// Smallest [Uint] that fits 2K bits.
        type DoubleK = U64;
        debug_assert!(DoubleK::BITS >= 2 * K);
        const K_SUB_ONE_BITMASK: DoubleK =
            DoubleK::ONE.shl_vartime(K - 1).wrapping_sub(&DoubleK::ONE);

        let (mut a, mut b) = (*self, *rhs);
        let (mut u, mut v) = (Int::<LIMBS>::ONE, Int::<LIMBS>::ZERO);

        let (mut sgn_a, mut sgn_b);

        let mut i = 0;
        while i < (2 * rhs.bits_vartime() - 1).div_ceil(K) {
            i += 1;

            // Construct a_ and b_ as the concatenation of the K most significant and the K least
            // significant bits of a and b, respectively. If those bits overlap, ... TODO
            let n = Self::const_max(2 * K, Self::const_max(a.bits(), b.bits()));

            let hi_a = a.shr(n - K - 1).resize::<{ DoubleK::LIMBS }>(); // top k+1 bits
            let lo_a = a.resize::<{ DoubleK::LIMBS }>().bitand(&K_SUB_ONE_BITMASK); // bottom k-1 bits
            let mut a_: DoubleK = hi_a.shl_vartime(K - 1).bitxor(&lo_a);

            let hi_b = b.shr(n - K - 1).resize::<{ DoubleK::LIMBS }>();
            let lo_b = b.resize::<{ DoubleK::LIMBS }>().bitand(&K_SUB_ONE_BITMASK);
            let mut b_: DoubleK = hi_b.shl_vartime(K - 1).bitxor(&lo_b);

            // Unit matrix
            let (mut f0, mut g0) = (SingleK::ONE, SingleK::ZERO);
            let (mut f1, mut g1) = (SingleK::ZERO, SingleK::ONE);

            // Compute the update matrix.
            let mut j = 0;
            while j < K - 1 {
                j += 1;

                // Only apply operations when b ≠ 0, otherwise do nothing.
                let b_is_non_zero = b_.is_nonzero();

                let a_odd = a_.is_odd();
                let a_lt_b = DoubleK::lt(&a_, &b_);

                // swap if a odd and a < b
                let do_swap = a_odd.and(a_lt_b).and(b_is_non_zero);
                DoubleK::conditional_swap(&mut a_, &mut b_, do_swap);
                SingleK::conditional_swap(&mut f0, &mut f1, do_swap);
                SingleK::conditional_swap(&mut g0, &mut g1, do_swap);

                // subtract a from b when a is odd and b is non-zero
                let do_sub = a_odd.and(b_is_non_zero);
                a_ = DoubleK::select(&a_, &a_.wrapping_sub(&b_), do_sub);
                f0 = SingleK::select(
                    &f0,
                    &f0.checked_sub(&f1).expect("no overflow"),
                    do_sub,
                );
                g0 = SingleK::select(
                    &g0,
                    &g0.checked_sub(&g1).expect("no overflow"),
                    do_sub,
                );

                // mul/div by 2 when b is non-zero.
                a_ = DoubleK::select(&a_, &a_.shr_vartime(1), b_is_non_zero);
                f1 = SingleK::select(&f1, &f1.shl_vartime(1), b_is_non_zero);
                g1 = SingleK::select(&g1, &g1.shl_vartime(1), b_is_non_zero);
            }

            let (new_a, new_b) = (
                Self::addmul_shr_k_sub_1::<K, { SingleK::LIMBS }>(a, b, f0, g0),
                Self::addmul_shr_k_sub_1::<K, { SingleK::LIMBS }>(a, b, f1, g1),
            );

            // Correct for case where `a` is negative.
            (a, sgn_a) = new_a.abs_sign();
            f0 = f0.wrapping_neg_if(sgn_a);
            g0 = g0.wrapping_neg_if(sgn_a);

            // Correct for case where `b` is negative.
            (b, sgn_b) = new_b.abs_sign();
            f1 = f1.wrapping_neg_if(sgn_b);
            g1 = g1.wrapping_neg_if(sgn_b);

            // Update u and v
            (u, v) = (
                u.checked_mul(&f0)
                    .expect("TODO")
                    .wrapping_add(&v.checked_mul(&g0).expect("TODO")),
                u.checked_mul(&f1)
                    .expect("TODO")
                    .wrapping_add(&v.checked_mul(&g1).expect("TODO")),
            );
        }

        (a, b, u, v)
    }
}

#[cfg(test)]
mod tests {
    use crate::{Random, Uint, U128};
    use rand_core::OsRng;

    #[test]
    fn test_new_gcd() {
        let x = U128::random(&mut OsRng);
        let y = U128::random(&mut OsRng);

        // make y odd:
        let y = Uint::select(&y, &(y + Uint::ONE), y.is_odd().not());

        // let inv_x = x.new_inv_mod_odd(&modulus).unwrap();
        let (x, gcd, a, b) = x.new_xgcd_odd_vartime(&y);

        assert_eq!(gcd, x.gcd(&y), "{} {} {} {}", x, gcd, a, b);
    }
}
