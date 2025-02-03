use crate::uint::bingcd::matrix::IntMatrix;
use crate::{Int, Uint};

impl<const LIMBS: usize> Uint<LIMBS> {
    /// Constructs a matrix `M` s.t. for `(A, B) = M(a,b)` it holds that
    /// - `gcd(A, B) = gcd(a, b)`, and
    /// - `A.bits() < a.bits()` and/or `B.bits() < b.bits()`.
    ///
    /// Moreover, it returns `log_upper_bound: u32` s.t. each element in `M` lies in the interval
    /// `(-2^log_upper_bound, 2^log_upper_bound]`.
    ///
    /// Assumes `iterations < Uint::<UPDATE_LIMBS>::BITS`.
    #[inline]
    pub(super) const fn restricted_extended_gcd<const UPDATE_LIMBS: usize>(
        mut a: Uint<LIMBS>,
        mut b: Uint<LIMBS>,
        iterations: u32,
    ) -> (IntMatrix<UPDATE_LIMBS>, u32) {
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
}
