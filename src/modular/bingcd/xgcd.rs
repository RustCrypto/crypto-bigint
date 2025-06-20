use crate::modular::bingcd::matrix::BinXgcdMatrix;
use crate::modular::bingcd::tools::const_max;
use crate::{ConstChoice, Int, NonZero, Odd, U64, U128, Uint};

/// Container for the raw output of the Binary XGCD algorithm.
pub(crate) struct RawOddUintBinxgcdOutput<const LIMBS: usize> {
    gcd: Odd<Uint<LIMBS>>,
    matrix: BinXgcdMatrix<LIMBS>,
}

impl<const LIMBS: usize> RawOddUintBinxgcdOutput<LIMBS> {
    /// Process raw output, constructing an [UintBinxgcdOutput] object.
    pub(crate) fn process(&mut self) -> OddUintBinxgcdOutput<LIMBS> {
        self.remove_matrix_factors();
        let (x, y) = self.bezout_coefficients();
        let (lhs_on_gcd, rhs_on_gcd) = self.quotients();
        OddUintBinxgcdOutput {
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
    fn remove_matrix_factors(&mut self) {
        let (lhs_div_gcd, rhs_div_gcd) = self.quotients();
        let (x, y, .., k, k_upper_bound) = self.matrix.as_elements_mut();
        if *k_upper_bound > 0 {
            *x = x.bounded_div_2k_mod_q(
                *k,
                *k_upper_bound,
                &rhs_div_gcd.to_odd().expect("odd by construction"),
            );
            *y = y.bounded_div_2k_mod_q(
                *k,
                *k_upper_bound,
                &lhs_div_gcd.to_odd().expect("odd by construction"),
            );
            *k = 0;
            *k_upper_bound = 0;
        }
    }

    /// Obtain the bezout coefficients `(x, y)` such that `lhs * x + rhs * y = gcd`.
    fn bezout_coefficients(&self) -> (Int<LIMBS>, Int<LIMBS>) {
        let (m00, m01, m10, m11, pattern, ..) = self.matrix.as_elements();
        let m10_sub_m00 = m10.wrapping_sub(m00);
        let m11_sub_m01 = m11.wrapping_sub(m01);
        let apply = Uint::lte(&m10_sub_m00, m00).and(Uint::lte(&m11_sub_m01, m01));
        let m00 = Uint::select(m00, &m10_sub_m00, apply)
            .wrapping_neg_if(apply.xor(pattern.not()))
            .as_int();
        let m01 = Uint::select(m01, &m11_sub_m01, apply)
            .wrapping_neg_if(apply.xor(pattern))
            .as_int();
        (m00, m01)
    }

    /// Obtain the quotients `lhs/gcd` and `rhs/gcd` from `matrix`.
    fn quotients(&self) -> (Uint<LIMBS>, Uint<LIMBS>) {
        let (.., rhs_div_gcd, lhs_div_gcd, _, _, _) = self.matrix.as_elements();
        (*lhs_div_gcd, *rhs_div_gcd)
    }
}

/// Output of the Binary XGCD algorithm applied to two [Uint]s.
pub type UintBinxgcdOutput<const LIMBS: usize> = BaseUintBinxgcdOutput<Uint<LIMBS>, LIMBS>;

/// Output of the Binary XGCD algorithm applied to two [`NonZero<Uint<LIMBS>>`]s.
pub type NonZeroUintBinxgcdOutput<const LIMBS: usize> =
    BaseUintBinxgcdOutput<NonZero<Uint<LIMBS>>, LIMBS>;

/// Output of the Binary XGCD algorithm applied to two [`Odd<Uint<LIMBS>>`]s.
pub type OddUintBinxgcdOutput<const LIMBS: usize> = BaseUintBinxgcdOutput<Odd<Uint<LIMBS>>, LIMBS>;

/// Container for the processed output of the Binary XGCD algorithm.
#[derive(Debug)]
pub struct BaseUintBinxgcdOutput<T: Copy, const LIMBS: usize> {
    pub gcd: T,
    pub x: Int<LIMBS>,
    pub y: Int<LIMBS>,
    pub lhs_on_gcd: Uint<LIMBS>,
    pub rhs_on_gcd: Uint<LIMBS>,
}

impl<T: Copy, const LIMBS: usize> BaseUintBinxgcdOutput<T, LIMBS> {
    /// Borrow the elements in this struct.
    pub fn to_components(&self) -> (T, Int<LIMBS>, Int<LIMBS>, Uint<LIMBS>, Uint<LIMBS>) {
        (self.gcd, self.x, self.y, self.lhs_on_gcd, self.rhs_on_gcd)
    }

    /// Mutably borrow the elements in this struct.
    pub fn as_components_mut(
        &mut self,
    ) -> (
        &mut T,
        &mut Int<LIMBS>,
        &mut Int<LIMBS>,
        &mut Uint<LIMBS>,
        &mut Uint<LIMBS>,
    ) {
        (
            &mut self.gcd,
            &mut self.x,
            &mut self.y,
            &mut self.lhs_on_gcd,
            &mut self.rhs_on_gcd,
        )
    }

    /// The greatest common divisor stored in this object.
    pub fn gcd(&self) -> T {
        self.gcd
    }

    /// Obtain a copy of the Bézout coefficients.
    pub fn bezout_coefficients(&self) -> (Int<LIMBS>, Int<LIMBS>) {
        (self.x, self.y)
    }

    /// Obtain a copy of the quotients `lhs/gcd` and `rhs/gcd`.
    pub fn quotients(&self) -> (Uint<LIMBS>, Uint<LIMBS>) {
        (self.lhs_on_gcd, self.rhs_on_gcd)
    }
}

/// Number of bits used by [Odd::<Uint<LIMBS>>::optimized_binxgcd] to represent a "compact" [Uint].
const SUMMARY_BITS: u32 = U64::BITS;

/// Number of limbs used to represent [Self::SUMMARY_BITS].
const SUMMARY_LIMBS: usize = U64::LIMBS;

/// Twice the number of limbs used to represent [Self::SUMMARY_BITS], i.e., two times
/// [Self::SUMMARY_LIMBS].
const DOUBLE_SUMMARY_LIMBS: usize = U128::LIMBS;

impl<const LIMBS: usize> Odd<Uint<LIMBS>> {
    /// The minimal number of binary GCD iterations required to guarantee successful completion.
    const MIN_BINGCD_ITERATIONS: u32 = 2 * Self::BITS - 1;

    /// Given `(self, rhs)`, computes `(g, x, y)` s.t. `self * x + rhs * y = g = gcd(self, rhs)`,
    /// leveraging the Binary Extended GCD algorithm.
    pub(crate) fn binxgcd_nz(&self, rhs: &NonZero<Uint<LIMBS>>) -> OddUintBinxgcdOutput<LIMBS> {
        let (lhs_, rhs_) = (self.as_ref(), rhs.as_ref());

        // The `binxgcd` subroutine requires `rhs` needs to be odd. We leverage the equality
        // gcd(lhs, rhs) = gcd(lhs, |lhs-rhs|) to deal with the case that `rhs` is even.
        let rhs_gt_lhs = Uint::gt(rhs_, lhs_);
        let rhs_is_even = rhs_.is_odd().not();
        let abs_lhs_sub_rhs = Uint::select(
            &lhs_.wrapping_sub(rhs_),
            &rhs_.wrapping_sub(lhs_),
            rhs_gt_lhs,
        );
        let rhs_ = Uint::select(rhs.as_ref(), &abs_lhs_sub_rhs, rhs_is_even)
            .to_odd()
            .expect("rhs is odd by construction");

        let mut output = self.binxgcd_(&rhs_);
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
    /// This function switches between the "classic" and "optimized" algorithm at a best-effort
    /// threshold. When using [Uint]s with `LIMBS` close to the threshold, it may be useful to
    /// manually test whether the classic or optimized algorithm is faster for your machine.
    pub(crate) fn binxgcd_(&self, rhs: &Self) -> RawOddUintBinxgcdOutput<LIMBS> {
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
    /// Ref: Pornin, Optimized Binary GCD for Modular Inversion, Algorithm 1.
    /// <https://eprint.iacr.org/2020/972.pdf>.
    pub(crate) fn classic_binxgcd(&self, rhs: &Self) -> RawOddUintBinxgcdOutput<LIMBS> {
        let (gcd, _, matrix) = self.partial_binxgcd_vartime::<LIMBS>(
            rhs.as_ref(),
            Self::MIN_BINGCD_ITERATIONS,
            ConstChoice::TRUE,
        );

        RawOddUintBinxgcdOutput { gcd, matrix }
    }

    /// Given `(self, rhs)`, computes `(g, x, y)` s.t. `self * x + rhs * y = g = gcd(self, rhs)`,
    /// leveraging the Binary Extended GCD algorithm.
    ///
    /// **Warning**: `self` and `rhs` must be contained in an [U128] or larger.
    ///
    /// Note: this algorithm becomes more efficient than the classical algorithm for [Uint]s with
    /// relatively many `LIMBS`. A best-effort threshold is presented in [Self::binxgcd_].
    ///
    /// Note: the full algorithm has an additional parameter; this function selects the best-effort
    /// value for this parameter. You might be able to further tune your performance by calling the
    /// [Self::optimized_bingcd_] function directly.
    ///
    /// Ref: Pornin, Optimized Binary GCD for Modular Inversion, Algorithm 2.
    /// <https://eprint.iacr.org/2020/972.pdf>.
    pub(crate) fn optimized_binxgcd(&self, rhs: &Self) -> RawOddUintBinxgcdOutput<LIMBS> {
        assert!(Self::BITS >= U128::BITS);
        self.optimized_binxgcd_::<SUMMARY_BITS, SUMMARY_LIMBS, DOUBLE_SUMMARY_LIMBS>(rhs)
    }

    /// Given `(self, rhs)`, computes `(g, x, y)`, s.t. `self * x + rhs * y = g = gcd(self, rhs)`,
    /// leveraging the optimized Binary Extended GCD algorithm.
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
    pub(crate) fn optimized_binxgcd_<const K: u32, const LIMBS_K: usize, const LIMBS_2K: usize>(
        &self,
        rhs: &Self,
    ) -> RawOddUintBinxgcdOutput<LIMBS> {
        let (mut a, mut b) = (*self.as_ref(), *rhs.as_ref());
        let mut matrix = BinXgcdMatrix::UNIT;

        let (mut a_sgn, mut b_sgn);
        let mut i = 0;
        while i < Self::MIN_BINGCD_ITERATIONS.div_ceil(K - 1) {
            // Loop invariants:
            //  i) each iteration of this loop, `a.bits() + b.bits()` shrinks by at least K-1,
            //     until `b = 0`.
            // ii) `a` is odd.
            i += 1;

            // Construct compact_a and compact_b as the summary of a and b, respectively.
            let b_bits = b.bits();
            let n = const_max(2 * K, const_max(a.bits(), b_bits));
            let compact_a = a.compact::<K, LIMBS_2K>(n);
            let compact_b = b.compact::<K, LIMBS_2K>(n);
            let b_eq_compact_b =
                ConstChoice::from_u32_le(b_bits, K - 1).or(ConstChoice::from_u32_eq(n, 2 * K));

            // Verify that `compact_a` and `compact_b` preserve the ordering of `a` and `b`.
            let a_cmp_b = Uint::cmp(&a, &b);
            let compact_a_cmp_compact_b = Uint::cmp(&compact_a, &compact_b);
            let compact_maintains_ordering =
                ConstChoice::from_i8_eq(a_cmp_b, compact_a_cmp_compact_b);

            // Compute the K-1 iteration update matrix from a_ and b_
            let (.., mut update_matrix) = compact_a
                .to_odd()
                .expect("a is always odd")
                .partial_binxgcd_vartime::<LIMBS_K>(&compact_b, K - 1, b_eq_compact_b);

            // Deal with the case that compacting loses the ordering of `(a, b)`. When this is the
            // case, multiplying `update_matrix` with `(a, b)` will map one of the two to a negative
            // value, which will break the algorithm. To resolve this, we observe that this case
            // can only occur whenever (at least) the top `K+1` bits of `a` and `b` are the same.
            // As a result, subtracting one from the other causes `a.bits() + b.bits()` to shrink by
            // at least `K+1 > K-1` (as required by the loop invariant). It thus suffices to replace
            // `update_matrix` with a matrix that represents subtracting one from the other.
            let a_lt_b = ConstChoice::from_i8_eq(a_cmp_b, -1);
            update_matrix = BinXgcdMatrix::select(
                &BinXgcdMatrix::get_subtraction_matrix(a_lt_b, K - 1),
                &update_matrix,
                compact_maintains_ordering,
            );

            // Update `a` and `b` using the update matrix
            let (updated_a, updated_b) = update_matrix.extended_apply_to((a, b));
            (a, a_sgn) = updated_a.wrapping_drop_extension();
            (b, b_sgn) = updated_b.wrapping_drop_extension();

            assert!(a_sgn.not().to_bool_vartime(), "a is never negative");
            assert!(b_sgn.not().to_bool_vartime(), "b is never negative");

            matrix = update_matrix.wrapping_mul_right(&matrix);

            // Cont. of dealing with the case that compacting loses the ordering of `(a, b)`.
            // When `a > b` -- and thus `b` is subtracted from `a` -- it could be that `a` is now
            // even. Since `a` should always be odd, we swap the two operands. Note that `b` must be
            // odd, since subtracting it from the odd `a` yielded an even number.
            let a_is_even = a.is_odd().not();
            Uint::conditional_swap(&mut a, &mut b, a_is_even);
            matrix.conditional_swap_rows(a_is_even)
        }

        let gcd = a
            .to_odd()
            .expect("gcd of an odd value with something else is always odd");

        RawOddUintBinxgcdOutput { gcd, matrix }
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
    pub(crate) fn partial_binxgcd_vartime<const UPDATE_LIMBS: usize>(
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
    fn binxgcd_step<const MATRIX_LIMBS: usize>(
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
    use crate::modular::bingcd::xgcd::OddUintBinxgcdOutput;
    use crate::{ConcatMixed, Gcd, Uint};
    use core::ops::Div;
    use num_traits::Zero;

    #[cfg(feature = "rand_core")]
    use rand_chacha::ChaChaRng;
    #[cfg(feature = "rand_core")]
    use rand_core::SeedableRng;

    mod test_extract_quotients {
        use crate::modular::bingcd::matrix::BinXgcdMatrix;
        use crate::modular::bingcd::xgcd::RawOddUintBinxgcdOutput;
        use crate::{ConstChoice, U64, Uint};

        fn raw_binxgcdoutput_setup<const LIMBS: usize>(
            matrix: BinXgcdMatrix<LIMBS>,
        ) -> RawOddUintBinxgcdOutput<LIMBS> {
            RawOddUintBinxgcdOutput {
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
        use crate::modular::bingcd::xgcd::RawOddUintBinxgcdOutput;
        use crate::{ConstChoice, Int, U64, Uint};

        #[test]
        fn test_derive_bezout_coefficients_unit() {
            let mut output = RawOddUintBinxgcdOutput {
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
            let mut output = RawOddUintBinxgcdOutput {
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
            assert_eq!(x, Int::from(-2i32));
            assert_eq!(y, Int::from(2i32));

            let mut output = RawOddUintBinxgcdOutput {
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
            assert_eq!(x, Int::from(1i32));
            assert_eq!(y, Int::from(-2i32));
        }

        #[test]
        fn test_derive_bezout_coefficients_removes_doublings_easy() {
            let mut output = RawOddUintBinxgcdOutput {
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

            let mut output = RawOddUintBinxgcdOutput {
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
            let mut output = RawOddUintBinxgcdOutput {
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

    /// Helper function to effectively test xgcd.
    fn test_xgcd<const LIMBS: usize, const DOUBLE: usize>(
        lhs: Uint<LIMBS>,
        rhs: Uint<LIMBS>,
        output: OddUintBinxgcdOutput<LIMBS>,
    ) where
        Uint<LIMBS>:
            Gcd<Output = Uint<LIMBS>> + ConcatMixed<Uint<LIMBS>, MixedOutput = Uint<DOUBLE>>,
    {
        // Test the gcd
        assert_eq!(lhs.gcd(&rhs), output.gcd, "{} {}", lhs, rhs);

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
        if lhs != rhs {
            assert!(x.abs() <= output.rhs_on_gcd.shr(1) || output.rhs_on_gcd.is_zero());
            assert!(y.abs() <= output.lhs_on_gcd.shr(1) || output.lhs_on_gcd.is_zero());
        }
    }

    #[cfg(feature = "rand_core")]
    fn make_rng() -> ChaChaRng {
        ChaChaRng::from_seed([0; 32])
    }

    mod test_binxgcd_nz {
        use crate::modular::bingcd::xgcd::tests::test_xgcd;
        use crate::{
            ConcatMixed, Gcd, Int, U64, U128, U192, U256, U384, U512, U768, U1024, U2048, U4096,
            U8192, Uint,
        };

        #[cfg(feature = "rand_core")]
        use super::make_rng;
        #[cfg(feature = "rand_core")]
        use crate::Random;

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

        #[cfg(feature = "rand_core")]
        fn binxgcd_nz_randomized_tests<const LIMBS: usize, const DOUBLE: usize>(iterations: u32)
        where
            Uint<LIMBS>:
                Gcd<Output = Uint<LIMBS>> + ConcatMixed<Uint<LIMBS>, MixedOutput = Uint<DOUBLE>>,
        {
            let mut rng = make_rng();
            for _ in 0..iterations {
                let x = Uint::random(&mut rng).bitor(&Uint::ONE);
                let y = Uint::random(&mut rng).saturating_add(&Uint::ONE);
                binxgcd_nz_test(x, y);
            }
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

            #[cfg(feature = "rand_core")]
            binxgcd_nz_randomized_tests(100);
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
        use crate::modular::bingcd::xgcd::tests::test_xgcd;
        use crate::{
            ConcatMixed, Gcd, Int, U64, U128, U192, U256, U384, U512, U768, U1024, U2048, U4096,
            U8192, Uint,
        };

        #[cfg(feature = "rand_core")]
        use super::make_rng;
        #[cfg(feature = "rand_core")]
        use crate::Random;

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

        #[cfg(feature = "rand_core")]
        fn classic_binxgcd_randomized_tests<const LIMBS: usize, const DOUBLE: usize>(
            iterations: u32,
        ) where
            Uint<LIMBS>:
                Gcd<Output = Uint<LIMBS>> + ConcatMixed<Uint<LIMBS>, MixedOutput = Uint<DOUBLE>>,
        {
            let mut rng = make_rng();
            for _ in 0..iterations {
                let x = Uint::<LIMBS>::random(&mut rng).bitor(&Uint::ONE);
                let y = Uint::<LIMBS>::random(&mut rng).bitor(&Uint::ONE);
                classic_binxgcd_test(x, y);
            }
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

            #[cfg(feature = "rand_core")]
            classic_binxgcd_randomized_tests(100);
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
        #[cfg(feature = "rand_core")]
        use super::make_rng;
        #[cfg(feature = "rand_core")]
        use crate::Random;

        use crate::modular::bingcd::xgcd::tests::test_xgcd;
        use crate::modular::bingcd::xgcd::{DOUBLE_SUMMARY_LIMBS, SUMMARY_BITS, SUMMARY_LIMBS};
        use crate::{
            ConcatMixed, Gcd, Int, U64, U128, U192, U256, U384, U512, U768, U1024, U2048, U4096,
            U8192, Uint,
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

        #[cfg(feature = "rand_core")]
        fn optimized_binxgcd_randomized_tests<const LIMBS: usize, const DOUBLE: usize>(
            iterations: u32,
        ) where
            Uint<LIMBS>:
                Gcd<Output = Uint<LIMBS>> + ConcatMixed<Uint<LIMBS>, MixedOutput = Uint<DOUBLE>>,
        {
            let mut rng = make_rng();
            for _ in 0..iterations {
                let x = Uint::<LIMBS>::random(&mut rng).bitor(&Uint::ONE);
                let y = Uint::<LIMBS>::random(&mut rng).bitor(&Uint::ONE);
                optimized_binxgcd_test(x, y);
            }
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

            #[cfg(feature = "rand_core")]
            optimized_binxgcd_randomized_tests(100);
        }

        #[test]
        fn test_optimized_binxgcd_edge_cases() {
            // If one of these tests fails, you have probably tweaked the SUMMARY_BITS,
            // SUMMARY_LIMBS or DOUBLE_SUMMARY_LIMBS settings. Please make sure to update these
            // tests accordingly.
            assert_eq!(SUMMARY_BITS, 64);
            assert_eq!(SUMMARY_LIMBS, U64::LIMBS);
            assert_eq!(DOUBLE_SUMMARY_LIMBS, U128::LIMBS);

            // Case #1: a > b but a.compact() < b.compact()
            let a = U256::from_be_hex(
                "1234567890ABCDEF80000000000000000000000000000000BEDCBA0987654321",
            );
            let b = U256::from_be_hex(
                "1234567890ABCDEF800000000000000000000000000000007EDCBA0987654321",
            );
            assert!(a > b);
            assert!(
                a.compact::<SUMMARY_BITS, DOUBLE_SUMMARY_LIMBS>(U256::BITS)
                    < b.compact::<SUMMARY_BITS, DOUBLE_SUMMARY_LIMBS>(U256::BITS)
            );
            optimized_binxgcd_test(a, b);

            // Case #2: a < b but a.compact() > b.compact()
            optimized_binxgcd_test(b, a);

            // Case #3: a > b but a.compact() = b.compact()
            let a = U256::from_be_hex(
                "1234567890ABCDEF80000000000000000000000000000000FEDCBA0987654321",
            );
            let b = U256::from_be_hex(
                "1234567890ABCDEF800000000000000000000000000000007EDCBA0987654321",
            );
            assert!(a > b);
            assert_eq!(
                a.compact::<SUMMARY_BITS, DOUBLE_SUMMARY_LIMBS>(U256::BITS),
                b.compact::<SUMMARY_BITS, DOUBLE_SUMMARY_LIMBS>(U256::BITS)
            );
            optimized_binxgcd_test(a, b);

            // Case #4: a < b but a.compact() = b.compact()
            optimized_binxgcd_test(b, a);
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
