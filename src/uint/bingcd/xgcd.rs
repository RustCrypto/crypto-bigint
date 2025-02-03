use crate::uint::bingcd::matrix::IntMatrix;
use crate::Uint;

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

        // Compute the update matrix.
        let mut matrix = IntMatrix::UNIT;
        let mut log_upper_bound = 0;
        let mut j = 0;
        while j < iterations {
            j += 1;

            let a_odd = a.is_odd();
            let a_lt_b = Uint::lt(&a, &b);

            // swap if a odd and a < b
            let do_swap = a_odd.and(a_lt_b);
            Uint::conditional_swap(&mut a, &mut b, do_swap);
            matrix.conditional_swap_rows(do_swap);

            // subtract a from b when a is odd
            a = Uint::select(&a, &a.wrapping_sub(&b), a_odd);
            matrix.conditional_subtract_bottom_row_from_top(a_odd);

            // Div `a` by 2 and double the right column of the matrix when both a ≠ 0 and b ≠ 0.
            let do_apply = a.is_nonzero().and(b.is_nonzero());
            a = Uint::select(&a, &a.shr_vartime(1), do_apply);
            matrix.conditional_double_bottom_row(do_apply);
            log_upper_bound = do_apply.select_u32(log_upper_bound, log_upper_bound + 1);
        }

        (matrix, log_upper_bound)
    }
}

#[cfg(test)]
mod tests {
    use crate::uint::bingcd::matrix::IntMatrix;
    use crate::{Uint, I64, U64};

    #[test]
    fn test_restricted_extended_gcd() {
        let a = U64::from_be_hex("AE693BF7BE8E5566");
        let b = U64::from_be_hex("CA048AFA63CD6A1F");
        let (matrix, iters) = Uint::restricted_extended_gcd(a, b, 5);
        assert_eq!(iters, 5);
        assert_eq!(
            matrix,
            IntMatrix::new(I64::from(5), I64::from(-2), I64::from(-4), I64::from(8))
        );
    }

    #[test]
    fn test_restricted_extended_gcd_stops_early() {
        // Stop before max_iters
        let a = U64::from_be_hex("000000000E8E5566");
        let b = U64::from_be_hex("0000000003CD6A1F");
        let (.., iters) = Uint::restricted_extended_gcd::<{I64::LIMBS}>(a, b, 60);
        assert_eq!(iters, 35);
    }
}
