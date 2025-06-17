use crate::modular::bingcd::matrix::IntMatrix;
use crate::{Odd, Uint};

impl<const LIMBS: usize> Odd<Uint<LIMBS>> {
    /// Executes the optimized Binary GCD inner loop.
    ///
    /// Ref: Pornin, Optimized Binary GCD for Modular Inversion, Algorithm 2.
    /// <https://eprint.iacr.org/2020/972.pdf>.
    ///
    /// The function outputs a matrix that can be used to reduce the `a` and `b` in the main loop.
    ///
    /// This implementation deviates slightly from the paper, in that it "runs in place", i.e.,
    /// executes iterations that do nothing, once `a` becomes zero. As a result, the main loop
    /// can no longer assume that all `iterations` are executed. As such, the `executed_iterations`
    /// are counted and additionally returned. Note that each element in `M` lies in the interval
    /// `(-2^executed_iterations, 2^executed_iterations]`.
    ///
    /// Assumes `iterations < Uint::<UPDATE_LIMBS>::BITS`.
    ///
    /// The function executes in time variable in `iterations`.
    #[inline]
    pub(crate) const fn partial_binxgcd_vartime<const UPDATE_LIMBS: usize>(
        &self,
        rhs: &Uint<LIMBS>,
        iterations: u32,
    ) -> (IntMatrix<UPDATE_LIMBS>, u32) {
        debug_assert!(iterations < Uint::<UPDATE_LIMBS>::BITS);
        // (self, rhs) corresponds to (b_, a_) in the Algorithm 1 notation.
        let (mut a, mut b) = (*rhs, *self.as_ref());

        // Compute the update matrix. This matrix corresponds with (f0, g0, f1, g1) in the paper.
        let mut matrix = IntMatrix::UNIT;
        let mut executed_iterations = 0;
        let mut j = 0;
        while j < iterations {
            j += 1;

            let a_odd = a.is_odd();
            let a_lt_b = Uint::lt(&a, &b);

            // swap if a odd and a < b
            let do_swap = a_odd.and(a_lt_b);
            Uint::conditional_swap(&mut a, &mut b, do_swap);
            matrix.conditional_swap_rows(do_swap);

            // subtract b from a when a is odd
            a = Uint::select(&a, &a.wrapping_sub(&b), a_odd);
            matrix.conditional_subtract_bottom_row_from_top(a_odd);

            // Div a by 2.
            let double = a.is_nonzero();
            // safe to vartime; shr_vartime is variable in the value of shift only. Since this shift
            // is a public constant, the constant time property of this algorithm is not impacted.
            a = a.shr_vartime(1);
            // Double the bottom row of the matrix when a was ≠ 0
            matrix.conditional_double_bottom_row(double);

            // Something happened in this iteration only when a was non-zero before being halved.
            executed_iterations = double.select_u32(executed_iterations, executed_iterations + 1);
        }

        (matrix, executed_iterations)
    }
}

#[cfg(test)]
mod tests {
    use crate::modular::bingcd::matrix::IntMatrix;
    use crate::{I64, U64};

    #[test]
    fn test_restricted_extended_gcd() {
        let a = U64::from_be_hex("CA048AFA63CD6A1F").to_odd().unwrap();
        let b = U64::from_be_hex("AE693BF7BE8E5566");
        let (matrix, iters) = a.partial_binxgcd_vartime(&b, 5);
        assert_eq!(iters, 5);
        assert_eq!(
            matrix,
            IntMatrix::new(I64::from(5), I64::from(-2), I64::from(-4), I64::from(8))
        );
    }

    #[test]
    fn test_restricted_extended_gcd_stops_early() {
        // Stop before max_iters
        let a = U64::from_be_hex("0000000003CD6A1F").to_odd().unwrap();
        let b = U64::from_be_hex("000000000E8E5566");
        let (.., iters) = a.partial_binxgcd_vartime::<{ U64::LIMBS }>(&b, 60);
        assert_eq!(iters, 35);
    }
}
