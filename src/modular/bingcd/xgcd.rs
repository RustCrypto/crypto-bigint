use crate::modular::bingcd::matrix::BinXgcdMatrix;
use crate::modular::bingcd::tools::const_max;
use crate::{ConstChoice, Int, NonZero, Odd, U64, U128, Uint};

/// Container for the raw output of the Binary XGCD algorithm.
pub(crate) struct OddUintBinxgcdOutput<const LIMBS: usize> {
    gcd: Odd<Uint<LIMBS>>,
    matrix: BinXgcdMatrix<LIMBS>,
}

impl<const LIMBS: usize> OddUintBinxgcdOutput<LIMBS> {
    /// Process raw output, constructing an [UintBinxgcdOutput] object.
    const fn process(&mut self) -> UintBinxgcdOutput<LIMBS> {
        self.remove_matrix_factors();
        let (x, y) = self.bezout_coefficients();
        let (lhs_on_gcd, rhs_on_gcd) = self.quotients();
        UintBinxgcdOutput {
            gcd: self.gcd,
            x,
            y,
            lhs_on_gcd,
            rhs_on_gcd,
        }
    }

    /// Divide `self.matrix` by `2^self.matrix.k`, i.e., remove the excess doublings from
    /// `self.matrix`.
    ///
    /// The performed divisions are modulo `lhs` and `rhs` to maintain the correctness of the XGCD
    /// state.
    ///
    /// This operation is 'fast' since it only applies the division to the top row of the matrix.
    /// This is allowed since it is assumed that `self.matrix * (lhs, rhs) = (gcd, 0)`; dividing
    /// the bottom row of the matrix by a constant has no impact since its inner-product with the
    /// input vector is zero.
    const fn remove_matrix_factors(&mut self) {
        let (lhs_div_gcd, rhs_div_gcd) = self.quotients();
        let (x, y, .., k, k_upper_bound) = self.matrix.as_elements_mut();
        if *k_upper_bound > 0 {
            *x = x.div_2k_mod_q(
                *k,
                *k_upper_bound,
                &rhs_div_gcd.to_odd().expect("odd by construction"),
            );
            *y = y.div_2k_mod_q(
                *k,
                *k_upper_bound,
                &lhs_div_gcd.to_odd().expect("odd by construction"),
            );
            *k = 0;
            *k_upper_bound = 0;
        }
    }

    /// Obtain the bezout coefficients `(x, y)` such that `lhs * x + rhs * y = gcd`.
    const fn bezout_coefficients(&self) -> (Int<LIMBS>, Int<LIMBS>) {
        let (m00, m01, ..) = self.matrix.to_elements_signed();
        (m00, m01)
    }

    /// Obtain the quotients `lhs/gcd` and `rhs/gcd` from `matrix`.
    const fn quotients(&self) -> (Uint<LIMBS>, Uint<LIMBS>) {
        let (.., rhs_div_gcd, lhs_div_gcd, _, _, _) = self.matrix.as_elements();
        (*lhs_div_gcd, *rhs_div_gcd)
    }
}

/// Container for the processed output of the Binary XGCD algorithm.
pub(crate) struct UintBinxgcdOutput<const LIMBS: usize> {
    pub(crate) gcd: Odd<Uint<LIMBS>>,
    x: Int<LIMBS>,
    y: Int<LIMBS>,
    lhs_on_gcd: Uint<LIMBS>,
    rhs_on_gcd: Uint<LIMBS>,
}

impl<const LIMBS: usize> UintBinxgcdOutput<LIMBS> {
    /// Obtain a copy of the Bézout coefficients.
    pub(crate) const fn bezout_coefficients(&self) -> (Int<LIMBS>, Int<LIMBS>) {
        (self.x, self.y)
    }

    /// Obtain a copy of the quotients `lhs/gcd` and `rhs/gcd`.
    pub(crate) const fn quotients(&self) -> (Uint<LIMBS>, Uint<LIMBS>) {
        (self.lhs_on_gcd, self.rhs_on_gcd)
    }
}

impl<const LIMBS: usize> Odd<Uint<LIMBS>> {
    /// The minimal number of binary GCD iterations required to guarantee successful completion.
    const MIN_BINGCD_ITERATIONS: u32 = 2 * Self::BITS - 1;

    /// Given `(self, rhs)`, computes `(g, x, y)` s.t. `self * x + rhs * y = g = gcd(self, rhs)`,
    /// leveraging the Binary Extended GCD algorithm.
    ///
    /// **Warning**: this algorithm is only guaranteed to work for `self` and `rhs` for which the
    /// msb is **not** set. May panic otherwise.
    pub(crate) const fn binxgcd_nz(&self, rhs: &NonZero<Uint<LIMBS>>) -> UintBinxgcdOutput<LIMBS> {
        // The `binxgcd` subroutine requires `rhs` needs to be odd. We leverage the equality
        // gcd(lhs, rhs) = gcd(lhs, |lhs-rhs|) to deal with the case that `rhs` is even.
        let (abs_lhs_sub_rhs, rhs_gt_lhs) =
            self.as_ref().wrapping_sub(rhs.as_ref()).as_int().abs_sign();
        let rhs_is_even = rhs.as_ref().is_odd().not();
        let rhs_ = Uint::select(rhs.as_ref(), &abs_lhs_sub_rhs, rhs_is_even)
            .to_odd()
            .expect("rhs is odd by construction");

        let mut output = self.binxgcd(&rhs_);
        output.remove_matrix_factors();

        // Modify the output to negate the transformation applied to the input.
        let matrix = &mut output.matrix;
        let case_one = rhs_is_even.and(rhs_gt_lhs);
        matrix.conditional_subtract_right_column_from_left(case_one);
        let case_two = rhs_is_even.and(rhs_gt_lhs.not());
        matrix.conditional_add_right_column_to_left(case_two);
        matrix.conditional_negate(case_two);

        output.process()
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
    pub(crate) const fn binxgcd(&self, rhs: &Self) -> OddUintBinxgcdOutput<LIMBS> {
        if LIMBS < 4 {
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
    pub(crate) const fn classic_binxgcd(&self, rhs: &Self) -> OddUintBinxgcdOutput<LIMBS> {
        let (gcd, _, matrix) = self.partial_binxgcd_vartime::<LIMBS>(
            rhs.as_ref(),
            Self::MIN_BINGCD_ITERATIONS,
            ConstChoice::TRUE,
        );

        OddUintBinxgcdOutput { gcd, matrix }
    }

    /// Given `(self, rhs)`, computes `(g, x, y)` s.t. `self * x + rhs * y = g = gcd(self, rhs)`,
    /// leveraging the Binary Extended GCD algorithm.
    ///
    /// **Warning**: this algorithm is only guaranteed to work for `self` and `rhs` for which the
    /// msb is **not** set. May panic otherwise. Furthermore, at `self` and `rhs` must contain at
    /// least 128 bits.
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
    pub(crate) const fn optimized_binxgcd(&self, rhs: &Self) -> OddUintBinxgcdOutput<LIMBS> {
        assert!(Self::BITS >= U128::BITS);
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
    ) -> OddUintBinxgcdOutput<LIMBS> {
        let (mut a, mut b) = (*self.as_ref(), *rhs.as_ref());
        let mut matrix = BinXgcdMatrix::UNIT;

        let (mut a_sgn, mut b_sgn);
        let mut i = 0;
        while i < Self::MIN_BINGCD_ITERATIONS.div_ceil(K - 1) {
            i += 1;

            // Construct a_ and b_ as the summary of a and b, respectively.
            let b_bits = b.bits();
            let n = const_max(2 * K, const_max(a.bits(), b_bits));
            let a_ = a.compact::<K, LIMBS_2K>(n);
            let b_ = b.compact::<K, LIMBS_2K>(n);
            let b_fits_in_compact =
                ConstChoice::from_u32_le(b_bits, K - 1).or(ConstChoice::from_u32_eq(n, 2 * K));

            // Compute the K-1 iteration update matrix from a_ and b_
            let (.., update_matrix) = a_
                .to_odd()
                .expect("a is always odd")
                .partial_binxgcd_vartime::<LIMBS_K>(&b_, K - 1, b_fits_in_compact);

            // Update `a` and `b` using the update matrix
            let (updated_a, updated_b) = update_matrix.wrapping_apply_to((a, b));
            (a, a_sgn) = updated_a.wrapping_drop_extension();
            (b, b_sgn) = updated_b.wrapping_drop_extension();

            // TODO: this is sketchy!
            matrix = update_matrix.wrapping_mul_right(&matrix);
            matrix.conditional_negate(a_sgn);
        }

        let gcd = a
            .to_odd()
            .expect("gcd of an odd value with something else is always odd");

        OddUintBinxgcdOutput { gcd, matrix }
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

#[cfg(test)]
mod tests {
    use crate::modular::bingcd::xgcd::UintBinxgcdOutput;
    use crate::{ConcatMixed, Gcd, Uint};
    use core::ops::Div;
    use rand_chacha::ChaChaRng;
    use rand_core::SeedableRng;

    mod test_extract_quotients {
        use crate::modular::bingcd::matrix::BinXgcdMatrix;
        use crate::modular::bingcd::xgcd::OddUintBinxgcdOutput;
        use crate::{ConstChoice, U64, Uint};

        fn raw_binxgcdoutput_setup<const LIMBS: usize>(
            matrix: BinXgcdMatrix<LIMBS>,
        ) -> OddUintBinxgcdOutput<LIMBS> {
            OddUintBinxgcdOutput {
                gcd: Uint::<LIMBS>::ONE.to_odd().unwrap(),
                matrix,
            }
        }

        #[test]
        fn test_extract_quotients_unit() {
            let output = raw_binxgcdoutput_setup(BinXgcdMatrix::<{ U64::LIMBS }>::UNIT);
            let (lhs_on_gcd, rhs_on_gcd) = output.quotients();
            assert_eq!(lhs_on_gcd, Uint::ONE);
            assert_eq!(rhs_on_gcd, Uint::ZERO);
        }

        #[test]
        fn test_extract_quotients_basic() {
            let output = raw_binxgcdoutput_setup(BinXgcdMatrix::<{ U64::LIMBS }>::new(
                Uint::ZERO,
                Uint::ZERO,
                Uint::from(5u32),
                Uint::from(7u32),
                ConstChoice::FALSE,
                0,
                0,
            ));
            let (lhs_on_gcd, rhs_on_gcd) = output.quotients();
            assert_eq!(lhs_on_gcd, Uint::from(7u32));
            assert_eq!(rhs_on_gcd, Uint::from(5u32));

            let output = raw_binxgcdoutput_setup(BinXgcdMatrix::<{ U64::LIMBS }>::new(
                Uint::ZERO,
                Uint::ZERO,
                Uint::from(7u32),
                Uint::from(5u32),
                ConstChoice::TRUE,
                0,
                0,
            ));
            let (lhs_on_gcd, rhs_on_gcd) = output.quotients();
            assert_eq!(lhs_on_gcd, Uint::from(5u32));
            assert_eq!(rhs_on_gcd, Uint::from(7u32));
        }
    }

    mod test_derive_bezout_coefficients {
        use crate::modular::bingcd::matrix::BinXgcdMatrix;
        use crate::modular::bingcd::xgcd::OddUintBinxgcdOutput;
        use crate::{ConstChoice, Int, U64, Uint};

        #[test]
        fn test_derive_bezout_coefficients_unit() {
            let mut output = OddUintBinxgcdOutput {
                gcd: Uint::ONE.to_odd().unwrap(),
                matrix: BinXgcdMatrix::<{ U64::LIMBS }>::UNIT,
            };
            output.remove_matrix_factors();
            let (x, y) = output.bezout_coefficients();
            assert_eq!(x, Int::ONE);
            assert_eq!(y, Int::ZERO);
        }

        #[test]
        fn test_derive_bezout_coefficients_basic() {
            let mut output = OddUintBinxgcdOutput {
                gcd: Uint::ONE.to_odd().unwrap(),
                matrix: BinXgcdMatrix::new(
                    U64::from(2u32),
                    U64::from(3u32),
                    U64::from(4u32),
                    U64::from(5u32),
                    ConstChoice::TRUE,
                    0,
                    0,
                ),
            };
            output.remove_matrix_factors();
            let (x, y) = output.bezout_coefficients();
            assert_eq!(x, Int::from(2i32));
            assert_eq!(y, Int::from(-3i32));

            let mut output = OddUintBinxgcdOutput {
                gcd: Uint::ONE.to_odd().unwrap(),
                matrix: BinXgcdMatrix::new(
                    U64::from(2u32),
                    U64::from(3u32),
                    U64::from(3u32),
                    U64::from(5u32),
                    ConstChoice::FALSE,
                    0,
                    1,
                ),
            };
            output.remove_matrix_factors();
            let (x, y) = output.bezout_coefficients();
            assert_eq!(x, Int::from(-2i32));
            assert_eq!(y, Int::from(3i32));
        }

        #[test]
        fn test_derive_bezout_coefficients_removes_doublings_easy() {
            let mut output = OddUintBinxgcdOutput {
                gcd: Uint::ONE.to_odd().unwrap(),
                matrix: BinXgcdMatrix::new(
                    U64::from(2u32),
                    U64::from(6u32),
                    U64::from(3u32),
                    U64::from(5u32),
                    ConstChoice::TRUE,
                    1,
                    1,
                ),
            };
            output.remove_matrix_factors();
            let (x, y) = output.bezout_coefficients();
            assert_eq!(x, Int::ONE);
            assert_eq!(y, Int::from(-3i32));

            let mut output = OddUintBinxgcdOutput {
                gcd: Uint::ONE.to_odd().unwrap(),
                matrix: BinXgcdMatrix::new(
                    U64::from(120u32),
                    U64::from(64u32),
                    U64::from(7u32),
                    U64::from(5u32),
                    ConstChoice::FALSE,
                    5,
                    6,
                ),
            };
            output.remove_matrix_factors();
            let (x, y) = output.bezout_coefficients();
            assert_eq!(x, Int::from(-9i32));
            assert_eq!(y, Int::from(2i32));
        }

        #[test]
        fn test_derive_bezout_coefficients_removes_doublings_for_odd_numbers() {
            let mut output = OddUintBinxgcdOutput {
                gcd: Uint::ONE.to_odd().unwrap(),
                matrix: BinXgcdMatrix::new(
                    U64::from(2u32),
                    U64::from(6u32),
                    U64::from(7u32),
                    U64::from(5u32),
                    ConstChoice::FALSE,
                    3,
                    7,
                ),
            };
            output.remove_matrix_factors();
            let (x, y) = output.bezout_coefficients();
            assert_eq!(x, Int::from(-2i32));
            assert_eq!(y, Int::from(2i32));
        }
    }

    mod test_partial_binxgcd {
        use crate::modular::bingcd::matrix::BinXgcdMatrix;
        use crate::{ConstChoice, Odd, U64};

        const A: Odd<U64> = U64::from_be_hex("CA048AFA63CD6A1F").to_odd().expect("odd");
        const B: U64 = U64::from_be_hex("AE693BF7BE8E5566");

        #[test]
        fn test_partial_binxgcd() {
            let (.., matrix) =
                A.partial_binxgcd_vartime::<{ U64::LIMBS }>(&B, 5, ConstChoice::TRUE);
            let (.., k, _) = matrix.as_elements();
            assert_eq!(k, 5);
            assert_eq!(
                matrix,
                BinXgcdMatrix::new(
                    U64::from(8u64),
                    U64::from(4u64),
                    U64::from(2u64),
                    U64::from(5u64),
                    ConstChoice::TRUE,
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

            let (computed_a, computed_b) = matrix.wrapping_apply_to((A.get(), B));
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

    /// Helper function to effectively test xgcd.
    fn test_xgcd<const LIMBS: usize, const DOUBLE: usize>(
        lhs: Uint<LIMBS>,
        rhs: Uint<LIMBS>,
        output: UintBinxgcdOutput<LIMBS>,
    ) where
        Uint<LIMBS>:
            Gcd<Output = Uint<LIMBS>> + ConcatMixed<Uint<LIMBS>, MixedOutput = Uint<DOUBLE>>,
    {
        // Test the gcd
        assert_eq!(lhs.gcd(&rhs), output.gcd);

        // Test the quotients
        assert_eq!(output.lhs_on_gcd, lhs.div(output.gcd.as_nz_ref()));
        assert_eq!(output.rhs_on_gcd, rhs.div(output.gcd.as_nz_ref()));

        // Test the Bezout coefficients for correctness
        let (x, y) = output.bezout_coefficients();
        assert_eq!(
            x.widening_mul_uint(&lhs) + y.widening_mul_uint(&rhs),
            output.gcd.resize().as_int(),
        );

        // Test the Bezout coefficients for minimality
        assert!(x.abs() <= rhs.div(output.gcd.as_nz_ref()));
        assert!(y.abs() <= lhs.div(output.gcd.as_nz_ref()));
    }

    fn make_rng() -> ChaChaRng {
        ChaChaRng::from_seed([0; 32])
    }

    mod test_binxgcd_nz {
        use crate::modular::bingcd::xgcd::tests::{make_rng, test_xgcd};
        use crate::{
            ConcatMixed, Gcd, Int, RandomMod, U64, U128, U192, U256, U384, U512, U768, U1024,
            U2048, U4096, U8192, Uint,
        };

        fn binxgcd_nz_test<const LIMBS: usize, const DOUBLE: usize>(
            lhs: Uint<LIMBS>,
            rhs: Uint<LIMBS>,
        ) where
            Uint<LIMBS>:
                Gcd<Output = Uint<LIMBS>> + ConcatMixed<Uint<LIMBS>, MixedOutput = Uint<DOUBLE>>,
        {
            let output = lhs.to_odd().unwrap().binxgcd_nz(&rhs.to_nz().unwrap());
            test_xgcd(lhs, rhs, output);
        }

        fn binxgcd_nz_tests<const LIMBS: usize, const DOUBLE: usize>()
        where
            Uint<LIMBS>:
                Gcd<Output = Uint<LIMBS>> + ConcatMixed<Uint<LIMBS>, MixedOutput = Uint<DOUBLE>>,
        {
            // Edge cases
            let odd_upper_bound = *Int::MAX.as_uint();
            let even_upper_bound = Int::MIN.abs();
            binxgcd_nz_test(Uint::ONE, Uint::ONE);
            binxgcd_nz_test(Uint::ONE, odd_upper_bound);
            binxgcd_nz_test(Uint::ONE, even_upper_bound);
            binxgcd_nz_test(odd_upper_bound, Uint::ONE);
            binxgcd_nz_test(odd_upper_bound, odd_upper_bound);
            binxgcd_nz_test(odd_upper_bound, even_upper_bound);

            // Randomized test cases
            let mut rng = make_rng();
            let bound = Int::MIN.as_uint().to_nz().unwrap();
            for _ in 0..100 {
                let x = Uint::<LIMBS>::random_mod(&mut rng, &bound).bitor(&Uint::ONE);
                let y = Uint::<LIMBS>::random_mod(&mut rng, &bound).saturating_add(&Uint::ONE);
                binxgcd_nz_test(x, y);
            }
        }

        #[test]
        fn test_binxgcd_nz() {
            binxgcd_nz_tests::<{ U64::LIMBS }, { U128::LIMBS }>();
            binxgcd_nz_tests::<{ U128::LIMBS }, { U256::LIMBS }>();
            binxgcd_nz_tests::<{ U192::LIMBS }, { U384::LIMBS }>();
            binxgcd_nz_tests::<{ U256::LIMBS }, { U512::LIMBS }>();
            binxgcd_nz_tests::<{ U384::LIMBS }, { U768::LIMBS }>();
            binxgcd_nz_tests::<{ U512::LIMBS }, { U1024::LIMBS }>();
            binxgcd_nz_tests::<{ U1024::LIMBS }, { U2048::LIMBS }>();
            binxgcd_nz_tests::<{ U2048::LIMBS }, { U4096::LIMBS }>();
            binxgcd_nz_tests::<{ U4096::LIMBS }, { U8192::LIMBS }>();
        }
    }

    mod test_classic_binxgcd {
        use crate::modular::bingcd::xgcd::tests::{make_rng, test_xgcd};
        use crate::{
            ConcatMixed, Gcd, Int, RandomMod, U64, U128, U192, U256, U384, U512, U768, U1024,
            U2048, U4096, U8192, Uint,
        };

        fn classic_binxgcd_test<const LIMBS: usize, const DOUBLE: usize>(
            lhs: Uint<LIMBS>,
            rhs: Uint<LIMBS>,
        ) where
            Uint<LIMBS>:
                Gcd<Output = Uint<LIMBS>> + ConcatMixed<Uint<LIMBS>, MixedOutput = Uint<DOUBLE>>,
        {
            let mut output = lhs
                .to_odd()
                .unwrap()
                .classic_binxgcd(&rhs.to_odd().unwrap());
            test_xgcd(lhs, rhs, output.process());
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
            let mut rng = make_rng();
            let bound = Int::MIN.as_uint().to_nz().unwrap();
            for _ in 0..100 {
                let x = Uint::<LIMBS>::random_mod(&mut rng, &bound).bitor(&Uint::ONE);
                let y = Uint::<LIMBS>::random_mod(&mut rng, &bound).bitor(&Uint::ONE);
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

    mod test_optimized_binxgcd {
        use crate::modular::bingcd::xgcd::tests::{make_rng, test_xgcd};
        use crate::{
            ConcatMixed, Gcd, Int, RandomMod, U128, U192, U256, U384, U512, U768, U1024, U2048,
            U4096, U8192, Uint,
        };

        fn optimized_binxgcd_test<const LIMBS: usize, const DOUBLE: usize>(
            lhs: Uint<LIMBS>,
            rhs: Uint<LIMBS>,
        ) where
            Uint<LIMBS>:
                Gcd<Output = Uint<LIMBS>> + ConcatMixed<Uint<LIMBS>, MixedOutput = Uint<DOUBLE>>,
        {
            let mut output = lhs
                .to_odd()
                .unwrap()
                .optimized_binxgcd(&rhs.to_odd().unwrap());
            test_xgcd(lhs, rhs, output.process());
        }

        fn optimized_binxgcd_tests<const LIMBS: usize, const DOUBLE: usize>()
        where
            Uint<LIMBS>:
                Gcd<Output = Uint<LIMBS>> + ConcatMixed<Uint<LIMBS>, MixedOutput = Uint<DOUBLE>>,
        {
            // Edge cases
            let upper_bound = *Int::MAX.as_uint();
            optimized_binxgcd_test(Uint::ONE, Uint::ONE);
            optimized_binxgcd_test(Uint::ONE, upper_bound);
            optimized_binxgcd_test(upper_bound, Uint::ONE);
            optimized_binxgcd_test(upper_bound, upper_bound);

            // Randomized test cases
            let mut rng = make_rng();
            let bound = Int::MIN.as_uint().to_nz().unwrap();
            for _ in 0..100 {
                let x = Uint::<LIMBS>::random_mod(&mut rng, &bound).bitor(&Uint::ONE);
                let y = Uint::<LIMBS>::random_mod(&mut rng, &bound).bitor(&Uint::ONE);
                optimized_binxgcd_test(x, y);
            }
        }

        #[test]
        fn test_optimized_binxgcd() {
            optimized_binxgcd_tests::<{ U128::LIMBS }, { U256::LIMBS }>();
            optimized_binxgcd_tests::<{ U192::LIMBS }, { U384::LIMBS }>();
            optimized_binxgcd_tests::<{ U256::LIMBS }, { U512::LIMBS }>();
            optimized_binxgcd_tests::<{ U384::LIMBS }, { U768::LIMBS }>();
            optimized_binxgcd_tests::<{ U512::LIMBS }, { U1024::LIMBS }>();
            optimized_binxgcd_tests::<{ U1024::LIMBS }, { U2048::LIMBS }>();
            optimized_binxgcd_tests::<{ U2048::LIMBS }, { U4096::LIMBS }>();
            optimized_binxgcd_tests::<{ U4096::LIMBS }, { U8192::LIMBS }>();
        }
    }
}
