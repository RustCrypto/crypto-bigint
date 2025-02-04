use crate::uint::bingcd::matrix::IntMatrix;
use crate::{Odd, Uint};

impl<const LIMBS: usize> Odd<Uint<LIMBS>> {
    /// Executes `iterations` reduction steps of the Binary Extended GCD algorithm to reduce
    /// `(self, rhs)` towards their GCD. Note: once the gcd is found, the extra iterations are
    /// performed. However, the algorithm has been constructed that additional iterations have no
    /// effect on the output of the function. Returns the (partially reduced) `(self*, rhs*)`.
    /// If `rhs* = 0`, `self*` contains the `gcd(self, rhs)`.
    ///
    /// Additionally, the matrix `M` is constructed s.t. `M * (self, rhs) = (self*, rhs*)`.
    /// This matrix contains the Bézout coefficients in its top left and bottom right corners.
    ///
    /// Lastly, returns `log_upper_bound`. Each element in `M` lies in the interval
    /// `(-2^log_upper_bound, 2^log_upper_bound]`.
    ///
    /// Requires `iterations < Uint::<UPDATE_LIMBS>::BITS` to prevent the bezout coefficients from
    /// overflowing.
    #[inline]
    pub(super) const fn partial_binxgcd<const UPDATE_LIMBS: usize>(
        &self,
        rhs: &Uint<LIMBS>,
        iterations: u32,
    ) -> (Self, Uint<LIMBS>, IntMatrix<UPDATE_LIMBS>, u32) {
        debug_assert!(iterations < Uint::<UPDATE_LIMBS>::BITS);
        let (mut a, mut b) = (*self.as_ref(), *rhs);

        // Compute the update matrix.
        let mut matrix = IntMatrix::UNIT;
        let mut log_upper_bound = 0;
        let mut j = 0;
        while j < iterations {
            j += 1;

            let b_odd = b.is_odd();
            let a_gt_b = Uint::gt(&a, &b);

            // swap if b odd and a > b
            let do_swap = b_odd.and(a_gt_b);
            Uint::conditional_swap(&mut a, &mut b, do_swap);
            matrix.conditional_swap_rows(do_swap);

            // subtract a from b when b is odd
            b = Uint::select(&b, &b.wrapping_sub(&a), b_odd);
            matrix.conditional_subtract_top_row_from_bottom(b_odd);

            // Div b by two and double the top row of the matrix when a, b ≠ 0.
            let do_apply = a.is_nonzero().and(b.is_nonzero());
            b = Uint::select(&b, &b.shr_vartime(1), do_apply);
            matrix.conditional_double_top_row(do_apply);
            log_upper_bound = do_apply.select_u32(log_upper_bound, log_upper_bound + 1);
        }

        (a.to_odd().expect("a is always odd"), b, matrix, log_upper_bound)
    }
}

#[cfg(test)]
mod tests {
    mod test_partial_binxgcd {
    use crate::uint::bingcd::matrix::IntMatrix;
    use crate::{I64, U64};

        #[test]
        fn test_partial_binxgcd() {
            let a = U64::from_be_hex("CA048AFA63CD6A1F").to_odd().unwrap();
            let b = U64::from_be_hex("AE693BF7BE8E5566");
            let (.., matrix, iters) = a.partial_binxgcd(&b, 5);
            assert_eq!(iters, 5);
            assert_eq!(
                matrix,
                IntMatrix::new(I64::from(8), I64::from(-4), I64::from(-2), I64::from(5))
            );
        }

        #[test]
        fn test_partial_binxgcd_stops_early() {
            // Stop before max_iters
            let a = U64::from_be_hex("0000000003CD6A1F").to_odd().unwrap();
            let b = U64::from_be_hex("000000000E8E5566");
            let (gcd, .., iters) = a.partial_binxgcd::<{ U64::LIMBS }>(&b, 60);
            assert_eq!(iters, 35);
            assert_eq!(gcd.get(), a.gcd(&b));
        }
    }
}
