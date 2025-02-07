use crate::uint::bingcd::matrix::IntMatrix;
use crate::uint::bingcd::tools::const_max;
use crate::{ConstChoice, Int, Odd, Uint};

impl<const LIMBS: usize> Int<LIMBS> {
    /// Compute `self / 2^k  mod q`. Executes in time variable in `k_bound`. This value should be
    /// chosen as an inclusive upperbound to the value of `k`.
    #[inline]
    const fn div_2k_mod_q(&self, k: u32, k_bound: u32, q: &Odd<Uint<LIMBS>>) -> Self {
        let (abs, sgn) = self.abs_sign();
        let abs_div_2k_mod_q = abs.div_2k_mod_q(k, k_bound, q);
        Int::new_from_abs_sign(abs_div_2k_mod_q, sgn).expect("no overflow")
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
            &floored_half.wrapping_add(half_mod_q),
            add_one_half,
        )
    }
}

impl<const LIMBS: usize> Odd<Uint<LIMBS>> {
    /// Given `(self, rhs)`, compute `(g, x, y)` s.t. `self * x + rhs * y = g = gcd(self, rhs)`.
    ///
    /// TODO: this only works for `self` and `rhs` that are <= Int::MAX.
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
            let a_ = a.compact::<K, LIMBS_2K>(n);
            let b_ = b.compact::<K, LIMBS_2K>(n);

            // Compute the K-1 iteration update matrix from a_ and b_
            let (.., update_matrix, log_upper_bound) = a_
                .to_odd()
                .expect("a is always odd")
                .partial_binxgcd_vartime::<LIMBS_K>(&b_, K - 1);

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
        let total_iterations = reduction_rounds * (K - 1);
        let IntMatrix { m00, m01, .. } = matrix;
        let x = m00.div_2k_mod_q(total_bound_shift, total_iterations, rhs);
        let y = m01.div_2k_mod_q(total_bound_shift, total_iterations, self);

        (
            a.to_odd()
                .expect("gcd of an odd value with something else is always odd"),
            x,
            y,
        )
    }

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
    ///
    /// TODO: this only works for `self` and `rhs` that are <= Int::MAX.
    #[inline]
    pub(super) const fn partial_binxgcd_vartime<const UPDATE_LIMBS: usize>(
        &self,
        rhs: &Uint<LIMBS>,
        iterations: u32,
    ) -> (Self, Uint<LIMBS>, IntMatrix<UPDATE_LIMBS>, u32) {
        debug_assert!(iterations < Uint::<UPDATE_LIMBS>::BITS);
        // (self, rhs) corresponds to (b_, a_) in the Algorithm 1 notation.
        let (mut a, mut b) = (*rhs, *self.as_ref());

        // Compute the update matrix. This matrix corresponds with (f0, g0, f1, g1) in the paper.
        let mut matrix = IntMatrix::UNIT;
        matrix.conditional_swap_rows(ConstChoice::TRUE);
        let mut executed_iterations = 0;
        let mut j = 0;
        while j < iterations {
            Self::binxgcd_step(&mut a, &mut b, &mut matrix, &mut executed_iterations);
            j += 1;
        }

        matrix.conditional_swap_rows(ConstChoice::TRUE);
        (
            b.to_odd().expect("b is always odd"),
            a,
            matrix,
            executed_iterations,
        )
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
    /// Ref: Pornin, Algorithm 2, L8-17, <https://eprint.iacr.org/2020/972.pdf>.
    #[inline]
    const fn binxgcd_step<const MATRIX_LIMBS: usize>(
        a: &mut Uint<LIMBS>,
        b: &mut Uint<LIMBS>,
        matrix: &mut IntMatrix<MATRIX_LIMBS>,
        executed_iterations: &mut u32,
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
        let double = a.is_nonzero();
        // safe to vartime; shr_vartime is variable in the value of shift only. Since this shift
        // is a public constant, the constant time property of this algorithm is not impacted.
        *a = a.shr_vartime(1);
        // Double the bottom row of the matrix when a was ≠ 0
        matrix.conditional_double_bottom_row(double);

        // Something happened in this iteration only when a was non-zero before being halved.
        *executed_iterations = double.select_u32(*executed_iterations, *executed_iterations + 1);
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
            let (.., matrix, iters) = a.partial_binxgcd_vartime(&b, 5);
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
            let (gcd, .., iters) = a.partial_binxgcd_vartime::<{ U64::LIMBS }>(&b, 60);
            assert_eq!(iters, 35);
            assert_eq!(gcd.get(), a.gcd(&b));
        }
    }

    mod test_binxgcd {
        use crate::{
            ConcatMixed, Gcd, Int, RandomMod, Uint, U1024, U128, U192, U2048, U256, U384, U4096,
            U512, U64, U768, U8192,
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
            assert_eq!(prod, binxgcd.resize().as_int())
        }

        fn binxgcd_tests<const LIMBS: usize, const DOUBLE: usize>()
        where
            Uint<LIMBS>:
                Gcd<Output = Uint<LIMBS>> + ConcatMixed<Uint<LIMBS>, MixedOutput = Uint<DOUBLE>>,
        {
            // upper bound
            let upper_bound = *Int::MAX.as_uint();

            // Edge cases
            binxgcd_test(Uint::ONE, Uint::ONE);
            binxgcd_test(Uint::ONE, upper_bound);
            binxgcd_test(upper_bound, Uint::ONE);
            binxgcd_test(upper_bound, upper_bound);

            // Randomized test cases
            let bound = upper_bound.wrapping_add(&Uint::ONE).to_nz().unwrap();
            for _ in 0..100 {
                let x = Uint::<LIMBS>::random_mod(&mut OsRng, &bound).bitor(&Uint::ONE);
                let y = Uint::<LIMBS>::random_mod(&mut OsRng, &bound).bitor(&Uint::ONE);
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
