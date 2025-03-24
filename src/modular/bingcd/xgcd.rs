use crate::modular::bingcd::matrix::BinXgcdMatrix;
use crate::{ConstChoice, Odd, Uint};

impl<const LIMBS: usize> Odd<Uint<LIMBS>> {
    /// Executes the optimized Binary GCD inner loop.
    ///
    /// Ref: Pornin, Optimized Binary GCD for Modular Inversion, Algorithm 2.
    /// <https://eprint.iacr.org/2020/972.pdf>.
    ///
    /// The function outputs the reduced values `(a, b)` for the input values `(self, rhs)` as well
    /// as the matrix that yields the former two when multiplied with the latter two.
    ///
    /// Note: this implementation deviates slightly from the paper, in that it can be instructed to
    /// "run in place" (i.e., execute iterations that do nothing) once `a` becomes zero.
    /// This is done by passing a truthy `halt_at_zero`.
    ///
    /// The function executes in time variable in `iterations`.
    #[inline]
    pub(crate) const fn partial_binxgcd_vartime<const UPDATE_LIMBS: usize>(
        &self,
        rhs: &Uint<LIMBS>,
        iterations: u32,
        halt_at_zero: ConstChoice,
    ) -> (Self, Uint<LIMBS>, BinXgcdMatrix<UPDATE_LIMBS>) {
        let (mut a, mut b) = (*self.as_ref(), *rhs);
        // This matrix corresponds with (f0, g0, f1, g1) in the paper.
        let mut matrix = BinXgcdMatrix::UNIT;

        // Compute the update matrix.
        // Note: to be consistent with the paper, the `binxgcd_step` algorithm requires the second
        // argument to be odd. Here, we have `a` odd, so we have to swap a and b before and after
        // calling the subroutine. The columns of the matrix have to be swapped accordingly.
        Uint::swap(&mut a, &mut b);
        matrix.swap_rows();

        let mut j = 0;
        while j < iterations {
            Self::binxgcd_step(&mut a, &mut b, &mut matrix, halt_at_zero);
            j += 1;
        }

        // Undo swap
        Uint::swap(&mut a, &mut b);
        matrix.swap_rows();

        let a = a.to_odd().expect("a is always odd");
        (a, b, matrix)
    }

    /// Binary XGCD update step.
    ///
    /// This is a condensed, constant time execution of the following algorithm:
    /// ```text
    /// if a mod 2 == 1
    ///    if a < b
    ///        (a, b) ← (b, a)
    ///        (f0, g0, f1, g1) ← (f1, g1, f0, g0)
    ///    a ← a - b
    ///    (f0, g0) ← (f0 - f1, g0 - g1)
    /// if a > 0
    ///     a ← a/2
    ///     (f1, g1) ← (2f1, 2g1)
    /// ```
    /// where `matrix` represents
    /// ```text
    ///  (f0 g0)
    ///  (f1 g1).
    /// ```
    ///
    /// Note: this algorithm assumes `b` to be an odd integer. The algorithm will likely not yield
    /// the correct result when this is not the case.
    ///
    /// Ref: Pornin, Algorithm 2, L8-17, <https://eprint.iacr.org/2020/972.pdf>.
    #[inline]
    const fn binxgcd_step<const MATRIX_LIMBS: usize>(
        a: &mut Uint<LIMBS>,
        b: &mut Uint<LIMBS>,
        matrix: &mut BinXgcdMatrix<MATRIX_LIMBS>,
        halt_at_zero: ConstChoice,
    ) {
        let a_odd = a.is_odd();
        let a_lt_b = Uint::lt(a, b);

        // swap if a odd and a < b
        let swap = a_odd.and(a_lt_b);
        Uint::conditional_swap(a, b, swap);
        matrix.conditional_swap_rows(swap);

        // subtract b from a when a is odd
        *a = a.wrapping_sub(&Uint::select(&Uint::ZERO, b, a_odd));
        matrix.conditional_subtract_bottom_row_from_top(a_odd);

        // Div a by 2.
        let double = a.is_nonzero().or(halt_at_zero.not());
        // safe to vartime; shr_vartime is variable in the value of shift only. Since this shift
        // is a public constant, the constant time property of this algorithm is not impacted.
        *a = a.shr_vartime(1);

        // Double the bottom row of the matrix when a was ≠ 0 and when not halting.
        matrix.conditional_double_bottom_row(double);
    }
}

#[cfg(all(test, not(miri)))]
mod tests {
    use crate::modular::bingcd::matrix::BinXgcdMatrix;
    use crate::{ConstChoice, I64, Odd, U64};

    const A: Odd<U64> = U64::from_be_hex("CA048AFA63CD6A1F").to_odd().expect("odd");
    const B: U64 = U64::from_be_hex("AE693BF7BE8E5566");

    #[test]
    fn test_partial_binxgcd() {
        let (.., matrix) = A.partial_binxgcd_vartime::<{ U64::LIMBS }>(&B, 5, ConstChoice::TRUE);
        let (.., k, _) = matrix.as_elements();
        assert_eq!(k, 5);
        assert_eq!(
            matrix,
            BinXgcdMatrix::new(
                I64::from(8i64),
                I64::from(-4i64),
                I64::from(-2i64),
                I64::from(5i64),
                5,
                5
            )
        );
    }

    #[test]
    fn test_partial_binxgcd_constructs_correct_matrix() {
        let target_a = U64::from_be_hex("1CB3FB3FA1218FDB").to_odd().unwrap();
        let target_b = U64::from_be_hex("0EA028AF0F8966B6");

        let (new_a, new_b, matrix) =
            A.partial_binxgcd_vartime::<{ U64::LIMBS }>(&B, 5, ConstChoice::TRUE);

        assert_eq!(new_a, target_a);
        assert_eq!(new_b, target_b);

        let (computed_a, computed_b) = matrix.extended_apply_to((A.get(), B));
        let computed_a = computed_a.wrapping_drop_extension().0;
        let computed_b = computed_b.wrapping_drop_extension().0;

        assert_eq!(computed_a, target_a);
        assert_eq!(computed_b, target_b);
    }

    const SMALL_A: Odd<U64> = U64::from_be_hex("0000000003CD6A1F").to_odd().expect("odd");
    const SMALL_B: U64 = U64::from_be_hex("000000000E8E5566");

    #[test]
    fn test_partial_binxgcd_halts() {
        let (gcd, _, matrix) =
            SMALL_A.partial_binxgcd_vartime::<{ U64::LIMBS }>(&SMALL_B, 60, ConstChoice::TRUE);
        let (.., k, k_upper_bound) = matrix.as_elements();
        assert_eq!(k, 35);
        assert_eq!(k_upper_bound, 60);
        assert_eq!(gcd.get(), SMALL_A.gcd(&SMALL_B));
    }

    #[test]
    fn test_partial_binxgcd_does_not_halt() {
        let (gcd, .., matrix) =
            SMALL_A.partial_binxgcd_vartime::<{ U64::LIMBS }>(&SMALL_B, 60, ConstChoice::FALSE);
        let (.., k, k_upper_bound) = matrix.as_elements();
        assert_eq!(k, 60);
        assert_eq!(k_upper_bound, 60);
        assert_eq!(gcd.get(), SMALL_A.gcd(&SMALL_B));
    }
}
