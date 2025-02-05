use crate::uint::bingcd::matrix::IntMatrix;
use crate::uint::bingcd::tools::const_max;
use crate::{ConstChoice, Int, Odd, Uint};

impl<const LIMBS: usize> Int<LIMBS> {
    /// Compute `self / 2^k  mod q`. Executes in time variable in `k_bound`. This value should be
    /// chosen as an inclusive upperbound to the value of `k`.
    #[inline]
    const fn div_2k_mod_q(&self, k: u32, k_bound: u32, q: &Odd<Uint<LIMBS>>) -> Self {
        let (abs, sgn) = self.abs_sign();
        let abs_div_2k_mod_q = abs.div_2k_mod_q(k, k_bound, &q);
        Int::new_from_abs_sign(abs_div_2k_mod_q,sgn,).expect("no overflow")
    }
}

impl<const LIMBS: usize> Uint<LIMBS> {
    /// Compute `self / 2^k  mod q`. Executes in time variable in `k_bound`. This value should be
    /// chosen as an inclusive upperbound to the value of `k`.
    #[inline]
    const fn div_2k_mod_q(mut self, k: u32, k_bound: u32, q: &Odd<Self>) -> Self {
        //        1  / 2      mod q
        // = (q + 1) / 2      mod q
        // = (q - 1) / 2  + 1 mod q
        // = floor(q / 2) + 1 mod q, since q is odd.
        let one_half_mod_q = q.as_ref().shr_vartime(1).wrapping_add(&Uint::ONE);
        let mut i = 0;
        while i < k_bound {
            // Apply only while i < k
            let apply = ConstChoice::from_u32_lt(i, k);
            self = Self::select(&self, &self.div_2_mod_q(&one_half_mod_q), apply);
            i += 1;
        }

        self
    }

    /// Compute `self / 2 mod q`.
    #[inline]
    const fn div_2_mod_q(self, half_mod_q: &Self) -> Self {
        // Floor-divide self by 2. When self was odd, add back 1/2 mod q.
        let add_one_half = self.is_odd();
        let floored_half = self.shr_vartime(1);
        Self::select(
            &floored_half,
            &floored_half.wrapping_add(&half_mod_q),
            add_one_half,
        )
    }
}

impl<const LIMBS: usize> Odd<Uint<LIMBS>> {
    /// Given `(self, rhs)`, compute `(g, x, y)` s.t. `self * x + rhs * y = g = gcd(self, rhs)`.
    pub const fn binxgcd<const K: u32, const LIMBS_K: usize, const LIMBS_2K: usize>(
        &self,
        rhs: &Self,
    ) -> (Self, Int<LIMBS>, Int<LIMBS>) {
        let (mut a, mut b) = (*self.as_ref(), *rhs.as_ref());

        let mut matrix = IntMatrix::UNIT;
        let mut i = 0;
        let mut total_bound_shift = 0;
        let reduction_rounds = (2 * Self::BITS - 1).div_ceil(K);
        while i < reduction_rounds {
            i += 1;

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
            matrix.conditional_negate_bottom_row(b_sgn);
            total_bound_shift += log_upper_bound;
        }

        // Extract the Bezout coefficients.
        let total_iterations = reduction_rounds * (K-1);
        let x = matrix.m00.div_2k_mod_q(total_bound_shift, total_iterations, &rhs);
        let y = matrix.m01.div_2k_mod_q(total_bound_shift, total_iterations, &self);

        (
            a.to_odd()
                .expect("gcd of an odd value with something else is always odd"),
            x,
            y,
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
        use rand_core::OsRng;

        fn binxgcd_test<const LIMBS: usize, const DOUBLE: usize>(lhs: Uint<LIMBS>, rhs: Uint<LIMBS>)
        where
            Uint<LIMBS>:
                Gcd<Output = Uint<LIMBS>> + ConcatMixed<Uint<LIMBS>, MixedOutput = Uint<DOUBLE>>,
        {
            let gcd = lhs.gcd(&rhs);
            let (binxgcd, x, y) = lhs
                .to_odd()
                .unwrap()
                .binxgcd::<64, { U64::LIMBS }, { U128::LIMBS }>(&rhs.to_odd().unwrap());
            assert_eq!(gcd, binxgcd);
            // test bezout coefficients
            let prod = x.widening_mul_uint(&lhs) + y.widening_mul_uint(&rhs);
            assert_eq!(
                prod,
                binxgcd.resize().as_int(),
                "{} {} {} {} {} {}",
                lhs,
                rhs,
                prod,
                binxgcd,
                x,
                y
            )
        }

        fn binxgcd_tests<const LIMBS: usize, const DOUBLE: usize>()
        where
            Uint<LIMBS>:
                Gcd<Output = Uint<LIMBS>> + ConcatMixed<Uint<LIMBS>, MixedOutput = Uint<DOUBLE>>,
        {
            // Edge cases
            binxgcd_test(Uint::ONE, Uint::ONE);
            binxgcd_test(Uint::ONE, Uint::MAX);
            binxgcd_test(Uint::MAX, Uint::ONE);
            binxgcd_test(Uint::MAX, Uint::MAX);
            binxgcd_test(
                Uint::from_be_hex("7BE417F8D79B2A7EAE8E4E9621C36FF3"),
                Uint::from_be_hex("02427A8560599FD5183B0375455A895F"),
            );

            // Randomized test cases
            for _ in 0..100 {
                let x = Uint::<LIMBS>::random(&mut OsRng).bitor(&Uint::ONE);
                let y = Uint::<LIMBS>::random(&mut OsRng).bitor(&Uint::ONE);
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
