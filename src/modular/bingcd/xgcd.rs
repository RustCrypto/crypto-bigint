use crate::modular::bingcd::matrix::IntMatrix;
use crate::modular::bingcd::tools::const_max;
use crate::{ConstChoice, Int, NonZero, Odd, Uint, U128, U64};

impl<const LIMBS: usize> Odd<Uint<LIMBS>> {
    /// The minimal number of binary GCD iterations required to guarantee successful completion.
    const MIN_BINGCD_ITERATIONS: u32 = 2 * Self::BITS - 1;

    /// Given `(self, rhs)`, computes `(g, x, y)` s.t. `self * x + rhs * y = g = gcd(self, rhs)`,
    /// leveraging the Binary Extended GCD algorithm.
    ///
    /// **Warning**: this algorithm is only guaranteed to work for `self` and `rhs` for which the
    /// msb is **not** set. May panic otherwise.
    pub(crate) const fn binxgcd_nz(
        &self,
        rhs: &NonZero<Uint<LIMBS>>,
    ) -> (Self, Int<LIMBS>, Int<LIMBS>) {
        // Note that for the `binxgcd` subroutine, `rhs` needs to be odd.
        //
        // We use the fact that gcd(a, b) = gcd(a, |a-b|) to
        // 1) convert the input (self, rhs) to (self, rhs') where rhs' is guaranteed odd,
        // 2) execute the xgcd algorithm on (self, rhs'), and
        // 3) recover the Bezout coefficients for (self, rhs) from the (self, rhs') output.

        let (abs_lhs_sub_rhs, rhs_gt_lhs) =
            self.as_ref().wrapping_sub(rhs.as_ref()).as_int().abs_sign();
        let rhs_is_even = rhs.as_ref().is_odd().not();
        let rhs_ = Uint::select(rhs.as_ref(), &abs_lhs_sub_rhs, rhs_is_even)
            .to_odd()
            .expect("rhs is odd by construction");

        let (gcd, mut x, mut y) = self.binxgcd(&rhs_);

        // At this point, we have one of the following three situations:
        // i.   gcd = lhs * x + (rhs - lhs) * y, if rhs is even and rhs > lhs
        // ii.  gcd = lhs * x + (lhs - rhs) * y, if rhs is even and rhs < lhs
        // iii. gcd = lhs * x + rhs * y, if rhs is odd

        // We can rearrange these terms to get the Bezout coefficients to the original (self, rhs)
        // input as follows:
        // i.   gcd = lhs * (x - y) + rhs * y, if rhs is even and rhs > lhs
        // ii.  gcd = lhs * (x + y) - y * rhs, if rhs is even and rhs < lhs
        // iii. gcd = lhs * x + rhs * y, if rhs is odd

        x = Int::select(&x, &x.wrapping_sub(&y), rhs_is_even.and(rhs_gt_lhs));
        x = Int::select(&x, &x.wrapping_add(&y), rhs_is_even.and(rhs_gt_lhs.not()));
        y = y.wrapping_neg_if(rhs_is_even.and(rhs_gt_lhs.not()));

        (gcd, x, y)
    }

    /// Given `(self, rhs)`, computes `(g, x, y)` s.t. `self * x + rhs * y = g = gcd(self, rhs)`,
    /// leveraging the Binary Extended GCD algorithm.
    ///
    /// **Warning**: this algorithm is only guaranteed to work for `self` and `rhs` for which the
    /// msb is **not** set. May panic otherwise.
    ///
    /// This function switches between the "classic" and "optimized" algorithm at a best-effort
    /// threshold. When using [Uint]s with `LIMBS` close to the threshold, it may be useful to
    /// manually test whether the classic or optimized algorithm is faster for your machine.
    pub(crate) const fn binxgcd(&self, rhs: &Self) -> (Self, Int<LIMBS>, Int<LIMBS>) {
        // todo: optimize threshold
        if LIMBS < 5 {
            self.classic_binxgcd(rhs)
        } else {
            self.optimized_binxgcd(rhs)
        }
    }

    /// Execute the classic Binary Extended GCD algorithm.
    ///
    /// Given `(self, rhs)`, computes `(g, x, y)` s.t. `self * x + rhs * y = g = gcd(self, rhs)`.
    ///
    /// **Warning**: this algorithm is only guaranteed to work for `self` and `rhs` for which the
    /// msb is **not** set. May panic otherwise.
    ///
    /// Ref: Pornin, Optimized Binary GCD for Modular Inversion, Algorithm 1.
    /// <https://eprint.iacr.org/2020/972.pdf>.
    pub(crate) const fn classic_binxgcd(&self, rhs: &Self) -> (Self, Int<LIMBS>, Int<LIMBS>) {
        let (gcd, _, matrix, total_bound_shift) = self.partial_binxgcd_vartime::<LIMBS>(
            rhs.as_ref(),
            Self::MIN_BINGCD_ITERATIONS,
            ConstChoice::TRUE,
        );

        // Extract the Bezout coefficients s.t. self * x + rhs + y = gcd
        let IntMatrix { m00, m01, .. } = matrix;
        let x = m00.div_2k_mod_q(total_bound_shift, Self::MIN_BINGCD_ITERATIONS, rhs);
        let y = m01.div_2k_mod_q(total_bound_shift, Self::MIN_BINGCD_ITERATIONS, self);

        (gcd, x, y)
    }

    /// Given `(self, rhs)`, computes `(g, x, y)` s.t. `self * x + rhs * y = g = gcd(self, rhs)`,
    /// leveraging the Binary Extended GCD algorithm.
    ///
    /// **Warning**: this algorithm is only guaranteed to work for `self` and `rhs` for which the
    /// msb is **not** set. May panic otherwise.
    ///
    /// Note: this algorithm becomes more efficient than the classical algorithm for [Uint]s with
    /// relatively many `LIMBS`. A best-effort threshold is presented in [Self::binxgcd].
    ///
    /// Note: the full algorithm has an additional parameter; this function selects the best-effort
    /// value for this parameter. You might be able to further tune your performance by calling the
    /// [Self::optimized_bingcd_] function directly.
    ///
    /// Ref: Pornin, Optimized Binary GCD for Modular Inversion, Algorithm 2.
    /// <https://eprint.iacr.org/2020/972.pdf>.
    pub(crate) const fn optimized_binxgcd(&self, rhs: &Self) -> (Self, Int<LIMBS>, Int<LIMBS>) {
        self.optimized_binxgcd_::<{ U64::BITS }, { U64::LIMBS }, { U128::LIMBS }>(rhs)
    }

    /// Given `(self, rhs)`, computes `(g, x, y)`, s.t. `self * x + rhs * y = g = gcd(self, rhs)`,
    /// leveraging the optimized Binary Extended GCD algorithm.
    ///
    /// **Warning**: this algorithm is only guaranteed to work for `self` and `rhs` for which the
    /// msb is **not** set. May panic otherwise.
    ///
    /// Ref: Pornin, Optimized Binary GCD for Modular Inversion, Algorithm 2.
    /// <https://eprint.iacr.org/2020/972.pdf>
    ///
    /// In summary, the optimized algorithm does not operate on `self` and `rhs` directly, but
    /// instead of condensed summaries that fit in few registers. Based on these summaries, an
    /// update matrix is constructed by which `self` and `rhs` are updated in larger steps.
    ///
    /// This function is generic over the following three values:
    /// - `K`: the number of bits used when summarizing `self` and `rhs` for the inner loop. The
    ///   `K+1` top bits and `K-1` least significant bits are selected. It is recommended to keep
    ///   `K` close to a (multiple of) the number of bits that fit in a single register.
    /// - `LIMBS_K`: should be chosen as the minimum number s.t. `Uint::<LIMBS>::BITS ≥ K`,
    /// - `LIMBS_2K`: should be chosen as the minimum number s.t. `Uint::<LIMBS>::BITS ≥ 2K`.
    pub(crate) const fn optimized_binxgcd_<
        const K: u32,
        const LIMBS_K: usize,
        const LIMBS_2K: usize,
    >(
        &self,
        rhs: &Self,
    ) -> (Self, Int<LIMBS>, Int<LIMBS>) {
        let (mut a, mut b) = (*self.as_ref(), *rhs.as_ref());
        let mut matrix = IntMatrix::UNIT;
        let mut total_doublings = 0;

        let (mut a_sgn, mut b_sgn);
        let mut i = 0;
        while i < Self::MIN_BINGCD_ITERATIONS.div_ceil(K) {
            i += 1;

            // Construct a_ and b_ as the summary of a and b, respectively.
            let b_bits = b.bits();
            let n = const_max(2 * K, const_max(a.bits(), b_bits));
            let a_ = a.compact::<K, LIMBS_2K>(n);
            let b_ = b.compact::<K, LIMBS_2K>(n);
            let b_fits_in_compact =
                ConstChoice::from_u32_le(b_bits, K - 1).or(ConstChoice::from_u32_eq(n, 2 * K));

            // Compute the K-1 iteration update matrix from a_ and b_
            let (.., update_matrix, doublings) = a_
                .to_odd()
                .expect("a is always odd")
                .partial_binxgcd_vartime::<LIMBS_K>(&b_, K - 1, b_fits_in_compact);

            // Update `a` and `b` using the update matrix
            let (updated_a, updated_b) = update_matrix.extended_apply_to((a, b));
            (a, a_sgn) = updated_a.div_2k(doublings).wrapping_drop_extension();
            (b, b_sgn) = updated_b.div_2k(doublings).wrapping_drop_extension();

            matrix = update_matrix.wrapping_mul_right(&matrix);
            matrix.conditional_negate_top_row(a_sgn);
            matrix.conditional_negate_bottom_row(b_sgn);
            total_doublings += doublings;
        }

        let gcd = a
            .to_odd()
            .expect("gcd of an odd value with something else is always odd");

        // Extract the Bezout coefficients s.t. self * x + rhs * y = gcd.
        let IntMatrix { m00, m01, .. } = matrix;
        let x = m00.div_2k_mod_q(total_doublings, Self::MIN_BINGCD_ITERATIONS, rhs);
        let y = m01.div_2k_mod_q(total_doublings, Self::MIN_BINGCD_ITERATIONS, self);

        (gcd, x, y)
    }

    /// Executes the optimized Binary GCD inner loop.
    ///
    /// Ref: Pornin, Optimized Binary GCD for Modular Inversion, Algorithm 2.
    /// <https://eprint.iacr.org/2020/972.pdf>.
    ///
    /// The function outputs the reduced values `(a, b)` for the input values `(self, rhs)` as well
    /// as the matrix that yields the former two when multiplied with the latter two.
    ///
    /// Additionally, the number doublings that were executed is returned. By construction, each
    /// element in `M` lies in the interval `(-2^doublings, 2^doublings]`.
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
    ) -> (Self, Uint<LIMBS>, IntMatrix<UPDATE_LIMBS>, u32) {
        let (mut a, mut b) = (*self.as_ref(), *rhs);
        // This matrix corresponds with (f0, g0, f1, g1) in the paper.
        let mut matrix = IntMatrix::UNIT;

        // Compute the update matrix.
        // Note: to be consistent with the paper, the `binxgcd_step` algorithm requires the second
        // argument to be odd. Here, we have `a` odd, so we have to swap a and b before and after
        // calling the subroutine. The columns of the matrix have to be swapped accordingly.
        Uint::swap(&mut a, &mut b);
        matrix.swap_rows();

        let mut doublings = 0;
        let mut j = 0;
        while j < iterations {
            Self::binxgcd_step::<UPDATE_LIMBS>(
                &mut a,
                &mut b,
                &mut matrix,
                &mut doublings,
                halt_at_zero,
            );
            j += 1;
        }

        // Undo swap
        Uint::swap(&mut a, &mut b);
        matrix.swap_rows();

        let a = a.to_odd().expect("a is always odd");
        (a, b, matrix, doublings)
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
        matrix: &mut IntMatrix<MATRIX_LIMBS>,
        executed_iterations: &mut u32,
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
        // Something happened in this iteration only when a was non-zero before being halved.
        *executed_iterations = double.select_u32(*executed_iterations, *executed_iterations + 1);
    }
}

#[cfg(test)]
mod tests {
    use crate::{ConcatMixed, Gcd, Int, Uint};

    mod test_partial_binxgcd {
        use crate::modular::bingcd::matrix::IntMatrix;
        use crate::{ConstChoice, I64, U64};

        #[test]
        fn test_partial_binxgcd() {
            let a = U64::from_be_hex("CA048AFA63CD6A1F").to_odd().unwrap();
            let b = U64::from_be_hex("AE693BF7BE8E5566");
            let (.., matrix, iters) =
                a.partial_binxgcd_vartime::<{ U64::LIMBS }>(&b, 5, ConstChoice::TRUE);
            assert_eq!(iters, 5);
            assert_eq!(
                matrix,
                IntMatrix::new(I64::from(8), I64::from(-4), I64::from(-2), I64::from(5))
            );
        }

        #[test]
        fn test_partial_binxgcd_constructs_correct_matrix() {
            let a = U64::from_be_hex("CA048AFA63CD6A1F").to_odd().unwrap();
            let b = U64::from_be_hex("AE693BF7BE8E5566");
            let (new_a, new_b, matrix, iters) =
                a.partial_binxgcd_vartime::<{ U64::LIMBS }>(&b, 5, ConstChoice::TRUE);
            assert_eq!(iters, 5);

            let (computed_a, computed_b) = matrix.extended_apply_to((a.get(), b));
            let computed_a = computed_a.div_2k(5).wrapping_drop_extension().0;
            let computed_b = computed_b.div_2k(5).wrapping_drop_extension().0;

            assert_eq!(
                new_a.get(),
                computed_a,
                "{} {} {} {}",
                new_a,
                new_b,
                computed_a,
                computed_b
            );
            assert_eq!(new_b, computed_b);
        }

        #[test]
        fn test_partial_binxgcd_halts() {
            // Stop before max_iters
            let a = U64::from_be_hex("0000000003CD6A1F").to_odd().unwrap();
            let b = U64::from_be_hex("000000000E8E5566");
            let (gcd, .., iters) =
                a.partial_binxgcd_vartime::<{ U64::LIMBS }>(&b, 60, ConstChoice::TRUE);
            assert_eq!(iters, 35);
            assert_eq!(gcd.get(), a.gcd(&b));
        }

        #[test]
        fn test_partial_binxgcd_does_not_halt() {
            // Stop before max_iters
            let a = U64::from_be_hex("0000000003CD6A1F").to_odd().unwrap();
            let b = U64::from_be_hex("000000000E8E5566");
            let (gcd, .., iters) =
                a.partial_binxgcd_vartime::<{ U64::LIMBS }>(&b, 60, ConstChoice::FALSE);
            assert_eq!(iters, 60);
            assert_eq!(gcd.get(), a.gcd(&b));
        }
    }

    /// Helper function to effectively test xgcd.
    fn test_xgcd<const LIMBS: usize, const DOUBLE: usize>(
        lhs: Uint<LIMBS>,
        rhs: Uint<LIMBS>,
        found_gcd: Uint<LIMBS>,
        x: Int<LIMBS>,
        y: Int<LIMBS>,
    ) where
        Uint<LIMBS>:
            Gcd<Output = Uint<LIMBS>> + ConcatMixed<Uint<LIMBS>, MixedOutput = Uint<DOUBLE>>,
    {
        // Test the gcd
        assert_eq!(lhs.gcd(&rhs), found_gcd);
        // Test the Bezout coefficients
        assert_eq!(
            x.widening_mul_uint(&lhs) + y.widening_mul_uint(&rhs),
            found_gcd.resize().as_int(),
        );
    }

    mod test_classic_binxgcd {
        use crate::modular::bingcd::xgcd::tests::test_xgcd;
        use crate::{
            ConcatMixed, Gcd, Int, RandomMod, Uint, U1024, U128, U192, U2048, U256, U384, U4096,
            U512, U64, U768, U8192,
        };
        use rand_core::OsRng;

        fn classic_binxgcd_test<const LIMBS: usize, const DOUBLE: usize>(
            lhs: Uint<LIMBS>,
            rhs: Uint<LIMBS>,
        ) where
            Uint<LIMBS>:
                Gcd<Output = Uint<LIMBS>> + ConcatMixed<Uint<LIMBS>, MixedOutput = Uint<DOUBLE>>,
        {
            let (binxgcd, x, y) = lhs
                .to_odd()
                .unwrap()
                .classic_binxgcd(&rhs.to_odd().unwrap());
            test_xgcd(lhs, rhs, binxgcd.get(), x, y);
        }

        fn classic_binxgcd_tests<const LIMBS: usize, const DOUBLE: usize>()
        where
            Uint<LIMBS>:
                Gcd<Output = Uint<LIMBS>> + ConcatMixed<Uint<LIMBS>, MixedOutput = Uint<DOUBLE>>,
        {
            // Edge cases
            let upper_bound = *Int::MAX.as_uint();
            classic_binxgcd_test(Uint::ONE, Uint::ONE);
            classic_binxgcd_test(Uint::ONE, upper_bound);
            classic_binxgcd_test(upper_bound, Uint::ONE);
            classic_binxgcd_test(upper_bound, upper_bound);

            // Randomized test cases
            let bound = Int::MIN.as_uint().to_nz().unwrap();
            for _ in 0..100 {
                let x = Uint::<LIMBS>::random_mod(&mut OsRng, &bound).bitor(&Uint::ONE);
                let y = Uint::<LIMBS>::random_mod(&mut OsRng, &bound).bitor(&Uint::ONE);
                classic_binxgcd_test(x, y);
            }
        }

        #[test]
        fn test_classic_binxgcd() {
            classic_binxgcd_tests::<{ U64::LIMBS }, { U128::LIMBS }>();
            classic_binxgcd_tests::<{ U128::LIMBS }, { U256::LIMBS }>();
            classic_binxgcd_tests::<{ U192::LIMBS }, { U384::LIMBS }>();
            classic_binxgcd_tests::<{ U256::LIMBS }, { U512::LIMBS }>();
            classic_binxgcd_tests::<{ U384::LIMBS }, { U768::LIMBS }>();
            classic_binxgcd_tests::<{ U512::LIMBS }, { U1024::LIMBS }>();
            classic_binxgcd_tests::<{ U1024::LIMBS }, { U2048::LIMBS }>();
            classic_binxgcd_tests::<{ U2048::LIMBS }, { U4096::LIMBS }>();
            classic_binxgcd_tests::<{ U4096::LIMBS }, { U8192::LIMBS }>();
        }
    }

    mod test_binxgcd {
        use crate::modular::bingcd::xgcd::tests::test_xgcd;
        use crate::{
            ConcatMixed, Gcd, Int, RandomMod, Uint, U1024, U128, U192, U2048, U256, U384, U4096,
            U512, U768, U8192,
        };
        use rand_core::OsRng;

        fn binxgcd_test<const LIMBS: usize, const DOUBLE: usize>(lhs: Uint<LIMBS>, rhs: Uint<LIMBS>)
        where
            Uint<LIMBS>:
                Gcd<Output = Uint<LIMBS>> + ConcatMixed<Uint<LIMBS>, MixedOutput = Uint<DOUBLE>>,
        {
            let (binxgcd, x, y) = lhs
                .to_odd()
                .unwrap()
                .optimized_binxgcd(&rhs.to_odd().unwrap());
            test_xgcd(lhs, rhs, binxgcd.get(), x, y);
        }

        fn binxgcd_tests<const LIMBS: usize, const DOUBLE: usize>()
        where
            Uint<LIMBS>:
                Gcd<Output = Uint<LIMBS>> + ConcatMixed<Uint<LIMBS>, MixedOutput = Uint<DOUBLE>>,
        {
            // Edge cases
            let upper_bound = *Int::MAX.as_uint();
            binxgcd_test(Uint::ONE, Uint::ONE);
            binxgcd_test(Uint::ONE, upper_bound);
            binxgcd_test(upper_bound, Uint::ONE);
            binxgcd_test(upper_bound, upper_bound);

            // Randomized test cases
            let bound = Int::MIN.as_uint().to_nz().unwrap();
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
