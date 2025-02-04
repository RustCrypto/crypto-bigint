use crate::uint::bingcd::matrix::IntMatrix;
use crate::uint::bingcd::tools::const_max;
use crate::{ConcatMixed, Odd, Uint};

impl<const LIMBS: usize> Odd<Uint<LIMBS>> {
    pub(super) fn binxgcd<const K: u32, const LIMBS_K: usize, const LIMBS_2K: usize, const DOUBLE: usize> (
        &self,
        rhs: &Uint<LIMBS>,
    ) -> (Self, IntMatrix<LIMBS>, u32)
    where
        Uint<LIMBS>: ConcatMixed<Uint<LIMBS>, MixedOutput=Uint<DOUBLE>>
    {
        let (mut a, mut b) = (*self.as_ref(), *rhs);

        let mut matrix = IntMatrix::UNIT;
        let mut i = 0;
        let mut total_bound_shift = 0;
        while i < (2 * Self::BITS - 1).div_ceil(K) {
            i += 1;

            // check identity
            // assert!(
            //     Int::eq(
            //         &matrix.m00.widening_mul_uint(&a).checked_add(&matrix.m01.widening_mul_uint(&b)).expect("no overflow"),
            //         &self.as_ref().resize().as_int()
            //     ).to_bool_vartime(),
            //     "{}", i
            // );
            // assert!(
            //     Int::eq(
            //         &matrix.m10.widening_mul_uint(&a).checked_add(&matrix.m11.widening_mul_uint(&b)).expect("no overflow"),
            //         &rhs.resize().as_int()
            //     ).to_bool_vartime(),
            //     "{}", i
            // );

            // Construct a_ and b_ as the summary of a and b, respectively.
            let n = const_max(2 * K, const_max(a.bits(), b.bits()));
            let a_ = a.compact::<LIMBS_2K>(n, K);
            let b_ = b.compact::<LIMBS_2K>(n, K);

            // Compute the K-1 iteration update matrix from a_ and b_
            let (.., update_matrix, log_upper_bound) = a_
                .to_odd()
                .expect("a is always odd")
                .partial_binxgcd::<LIMBS_K>(&b_, K - 1);

            // Update `a` and `b` using the update matrix
            let (updated_a, updated_b) = update_matrix.extended_apply_to((a, b));

            let (a_sgn, b_sgn);
            (a, a_sgn) = updated_a
                .div_2k(log_upper_bound)
                .drop_extension()
                .expect("extension is zero");
            (b, b_sgn) = updated_b
                .div_2k(log_upper_bound)
                .drop_extension()
                .expect("extension is zero");

            matrix = update_matrix.checked_mul_right(&matrix);
            matrix.conditional_negate_top_row(a_sgn);
            matrix.conditional_double_top_row(b_sgn);

            total_bound_shift += log_upper_bound;

            // check identity
            // assert!(
            //     Int::eq(
            //         &matrix.m00.widening_mul_uint(&a).checked_add(&matrix.m01.widening_mul_uint(&b)).expect("no overflow"),
            //         &self.as_ref().resize().as_int()
            //     ).to_bool_vartime(),
            //     "{} {}", i, total_bound_shift
            // );
            // assert!(
            //     Int::eq(
            //         &matrix.m10.widening_mul_uint(&a).checked_add(&matrix.m11.widening_mul_uint(&b)).expect("no overflow"),
            //         &rhs.resize().as_int()
            //     ).to_bool_vartime(),
            //     "{} {}", i, total_bound_shift
            // );
        }

        (
            a.to_odd()
                .expect("gcd of an odd value with something else is always odd"),
            matrix,
            total_bound_shift
        )
    }

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

        (
            a.to_odd().expect("a is always odd"),
            b,
            matrix,
            log_upper_bound,
        )
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

    mod test_binxgcd {
        use crate::{
            ConcatMixed, Gcd, Random, Uint, U1024, U128, U192, U2048, U256, U384, U4096, U512, U64,
            U768, U8192,
        };
        use core::ops::Div;
        use rand_core::OsRng;

        fn binxgcd_test<const LIMBS: usize, const DOUBLE: usize>(lhs: Uint<LIMBS>, rhs: Uint<LIMBS>)
        where
            Uint<LIMBS>:
                Gcd<Output = Uint<LIMBS>> + ConcatMixed<Uint<LIMBS>, MixedOutput = Uint<DOUBLE>>,
        {
            let gcd = lhs.gcd(&rhs);
            let (binxgcd, matrix, total_shift) = lhs
                .to_odd()
                .unwrap()
                .binxgcd::<64, { U64::LIMBS }, { U128::LIMBS }, DOUBLE>(&rhs);
            assert_eq!(gcd, binxgcd);
            // test divisors
            assert_eq!(matrix.m11.abs(), lhs.div(gcd));
            assert_eq!(matrix.m10.abs(), rhs.div(gcd));
            // test bezout coefficients
            let prod = matrix.m00.widening_mul_uint(&lhs) + matrix.m01.widening_mul_uint(&rhs);
            assert_eq!(
                prod.shr(total_shift),
                binxgcd.resize().as_int(),
                "{} {} {} {} {} {} {}",
                lhs,
                rhs,
                prod,
                binxgcd,
                matrix.m00,
                matrix.m01,
                total_shift
            )
        }

        fn binxgcd_tests<const LIMBS: usize, const DOUBLE: usize>()
        where
            Uint<LIMBS>:
                Gcd<Output = Uint<LIMBS>> + ConcatMixed<Uint<LIMBS>, MixedOutput = Uint<DOUBLE>>,
        {
            // Edge cases
            // binxgcd_test(Uint::ONE, Uint::ZERO);
            // binxgcd_test(Uint::ONE, Uint::ONE);
            // // binxgcd_test(Uint::ONE, Uint::MAX);
            // binxgcd_test(Uint::MAX, Uint::ZERO);
            // // binxgcd_test(Uint::MAX, Uint::ONE);
            // binxgcd_test(Uint::MAX, Uint::MAX);
            binxgcd_test(
                Uint::from_be_hex("7BE417F8D79B2A7EAE8E4E9621C36FF3"),
                Uint::from_be_hex("02427A8560599FD5183B0375455A895F"),
            );

            // Randomized test cases
            for _ in 0..100 {
                let x = Uint::<LIMBS>::random(&mut OsRng).bitor(&Uint::ONE);
                let y = Uint::<LIMBS>::random(&mut OsRng);
                binxgcd_test(x, y);
            }
        }

        #[test]
        fn test_binxgcd() {
            // Cannot be applied to U64
            binxgcd_tests::<{ U128::LIMBS }, { U256::LIMBS }>();
            binxgcd_tests::<{ U192::LIMBS }, { U384::LIMBS }>();
            binxgcd_tests::<{ U256::LIMBS }, { U512::LIMBS }>();
            binxgcd_tests::<{ U384::LIMBS }, { U768::LIMBS }>();
            binxgcd_tests::<{ U512::LIMBS }, { U1024::LIMBS }>();
            binxgcd_tests::<{ U1024::LIMBS }, { U2048::LIMBS }>();
            binxgcd_tests::<{ U2048::LIMBS }, { U4096::LIMBS }>();
            binxgcd_tests::<{ U4096::LIMBS }, { U8192::LIMBS }>();
        }
    }
}
