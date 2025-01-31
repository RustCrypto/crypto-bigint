//! This module implements (a constant variant of) the Optimized Extended Binary GCD algorithm,
//! which is described by Pornin as Algorithm 2 in "Optimized Binary GCD for Modular Inversion".
//! Ref: <https://eprint.iacr.org/2020/972.pdf>

use crate::uint::bingcd::matrix::IntMatrix;
use crate::{ConstChoice, Int, NonZero, Odd, Uint, I64, U128};

mod extension;
mod matrix;

/// `const` equivalent of `u32::max(a, b)`.
const fn max(a: u32, b: u32) -> u32 {
    ConstChoice::from_u32_lt(a, b).select_u32(a, b)
}

/// `const` equivalent of `u32::min(a, b)`.
const fn min(a: u32, b: u32) -> u32 {
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

    /// Computes `gcd(self, rhs)`, leveraging the Binary GCD algorithm.
    /// Is efficient only for relatively small `LIMBS`.
    #[inline]
    const fn odd_bingcd_small(mut a: Uint<LIMBS>, b: &Odd<Uint<LIMBS>>) -> Uint<LIMBS> {
        let mut b = *b.as_ref();
        let mut j = 0;
        while j < Uint::<LIMBS>::BITS {
            j += 1;

            let a_odd = a.is_odd();

            // swap if a odd and a < b
            let a_lt_b = Uint::lt(&a, &b);
            let do_swap = a_odd.and(a_lt_b);
            Uint::conditional_swap(&mut a, &mut b, do_swap);

            // subtract b from a when a is odd
            a = Uint::select(&a, &a.wrapping_sub(&b), a_odd);

            // Div a by two when b ≠ 0, otherwise do nothing.
            let do_apply = b.is_nonzero();
            a = Uint::select(&a, &a.shr_vartime(1), do_apply);
        }

        b
    }

    /// Constructs a matrix `M` s.t. for `(A, B) = M(a,b)` it holds that
    /// - `gcd(A, B) = gcd(a, b)`, and
    /// - `A.bits() < a.bits()` and/or `B.bits() < b.bits()`.
    ///
    /// Moreover, it returns `log_upper_bound: u32` s.t. each element in `M` lies in the interval
    /// `(-2^log_upper_bound, 2^log_upper_bound]`.
    ///
    /// Assumes `iterations < Uint::<UPDATE_LIMBS>::BITS`.
    #[inline]
    const fn restricted_extended_gcd<const UPDATE_LIMBS: usize>(
        mut a: Uint<LIMBS>,
        mut b: Uint<LIMBS>,
        iterations: u32,
    ) -> (IntMatrix<UPDATE_LIMBS, 2>, u32) {
        debug_assert!(iterations < Uint::<UPDATE_LIMBS>::BITS);

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

        (IntMatrix::new(f00, f01, f10, f11), log_upper_bound)
    }

    /// Compute the greatest common divisor of `self` and `rhs`.
    pub const fn bingcd(&self, rhs: &Self) -> Self {
        // Account for the case where rhs is zero
        let rhs_is_zero = rhs.is_nonzero().not();
        let rhs_ = Uint::select(rhs, &Uint::ONE, rhs_is_zero)
            .to_nz()
            .expect("rhs is non zero by construction");
        let result = self.bingcd_nonzero(&rhs_);
        Uint::select(&result, self, rhs_is_zero)
    }

    /// Compute the greatest common divisor of `self` and `rhs`, where `rhs` is known to be nonzero.
    const fn bingcd_nonzero(&self, rhs: &NonZero<Self>) -> Self {
        // Leverage two GCD identity rules to make self and rhs odd.
        // 1) gcd(2a, 2b) = 2 * gcd(a, b)
        // 2) gcd(a, 2b) = gcd(a, b) if a is odd.
        let i = self.is_nonzero().select_u32(0, self.trailing_zeros());
        let j = rhs
            .as_ref()
            .is_nonzero()
            .select_u32(0, rhs.as_ref().trailing_zeros());
        let k = min(i, j);

        Self::odd_bingcd(
            &self.shr(i),
            &rhs.as_ref()
                .shr(j)
                .to_odd()
                .expect("rhs is odd by construction"),
        )
        .shl(k)
    }

    /// Compute the greatest common divisor of `self` and `rhs`, where `rhs` is known to be odd.
    #[inline(always)]
    const fn odd_bingcd(&self, rhs: &Odd<Self>) -> Self {
        /// Window size.
        const K: u32 = 62;
        /// Smallest [Int] that fits a K-bit [Uint].
        type SingleK = I64;
        /// Smallest [Uint] that fits 2K bits.
        type DoubleK = U128;

        let (mut a, mut b) = (*self, *rhs.as_ref());

        let mut i = 0;
        while i < (2 * Self::BITS - 1).div_ceil(K) {
            i += 1;

            // Construct a_ and b_ as the summary of a and b, respectively.
            let n = max(2 * K, max(a.bits(), b.bits()));
            let a_: DoubleK = a.compact(n, K);
            let b_: DoubleK = b.compact(n, K);

            // Compute the K-1 iteration update matrix from a_ and b_
            let (matrix, used_increments) =
                Uint::restricted_extended_gcd::<{ SingleK::LIMBS }>(a_, b_, K - 1);

            // Update `a` and `b` using the update matrix
            let (updated_a, updated_b) = matrix.extended_apply_to((a, b));

            a = updated_a
                .div_2k(used_increments)
                .abs_drop_extension()
                .expect("extension is zero");
            b = updated_b
                .div_2k(used_increments)
                .abs_drop_extension()
                .expect("extension is zero");
        }

        b
    }
}

#[cfg(feature = "rand_core")]
#[cfg(test)]
mod tests {
    use rand_core::OsRng;

    use crate::{Gcd, Random, Uint, U1024, U16384, U2048, U256, U4096, U512, U8192};

    fn gcd_comparison_test<const LIMBS: usize>(lhs: Uint<LIMBS>, rhs: Uint<LIMBS>)
    where
        Uint<LIMBS>: Gcd<Output = Uint<LIMBS>>,
    {
        let gcd = lhs.gcd(&rhs);
        let bingcd = lhs.bingcd(&rhs);
        assert_eq!(gcd, bingcd);
    }

    fn test_new_gcd<const LIMBS: usize>()
    where
        Uint<LIMBS>: Gcd<Output = Uint<LIMBS>>,
    {
        // some basic test
        gcd_comparison_test(Uint::ZERO, Uint::ZERO);
        gcd_comparison_test(Uint::ZERO, Uint::ONE);
        gcd_comparison_test(Uint::ZERO, Uint::MAX);
        gcd_comparison_test(Uint::ONE, Uint::ZERO);
        gcd_comparison_test(Uint::ONE, Uint::ONE);
        gcd_comparison_test(Uint::ONE, Uint::MAX);
        gcd_comparison_test(Uint::MAX, Uint::ZERO);
        gcd_comparison_test(Uint::MAX, Uint::ONE);
        gcd_comparison_test(Uint::MAX, Uint::MAX);

        for _ in 0..100 {
            let x = Uint::<LIMBS>::random(&mut OsRng);
            let mut y = Uint::<LIMBS>::random(&mut OsRng);

            y = Uint::select(&(y.wrapping_add(&Uint::ONE)), &y, y.is_odd());

            gcd_comparison_test(x, y);
        }
    }

    #[test]
    fn testing() {
        test_new_gcd::<{ U256::LIMBS }>();
        test_new_gcd::<{ U512::LIMBS }>();
        test_new_gcd::<{ U1024::LIMBS }>();
        test_new_gcd::<{ U2048::LIMBS }>();
        test_new_gcd::<{ U4096::LIMBS }>();
        test_new_gcd::<{ U8192::LIMBS }>();
        test_new_gcd::<{ U16384::LIMBS }>();
    }
}
