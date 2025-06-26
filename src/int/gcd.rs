//! This module implements (a constant variant of) the Optimized Extended Binary GCD algorithm,
//! which is described by Pornin in "Optimized Binary GCD for Modular Inversion".
//! Ref: <https://eprint.iacr.org/2020/972.pdf>

use crate::const_choice::u32_min;
use crate::uint::gcd::OddUintXgcdOutput;
use crate::{
    ConstChoice, Gcd, Int, NonZero, NonZeroInt, NonZeroUint, Odd, OddInt, OddUint, Uint, Xgcd,
};

impl<const LIMBS: usize> Int<LIMBS> {
    /// Compute the gcd of `self` and `rhs` leveraging the Binary GCD algorithm.
    pub const fn bingcd(&self, rhs: &Self) -> Uint<LIMBS> {
        self.abs().bingcd(&rhs.abs())
    }

    /// Compute the gcd of `self` and `rhs` leveraging the Binary GCD algorithm.
    ///
    /// Executes in variable time w.r.t. all input parameters.
    pub const fn bingcd_vartime(&self, rhs: &Self) -> Uint<LIMBS> {
        self.abs().bingcd_vartime(&rhs.abs())
    }

    /// Executes the Binary Extended GCD algorithm.
    ///
    /// Given `(self, rhs)`, computes `(g, x, y)`, s.t. `self * x + rhs * y = g = gcd(self, rhs)`.
    pub const fn binxgcd(&self, rhs: &Self) -> IntXgcdOutput<LIMBS> {
        // Make sure `self` and `rhs` are nonzero.
        let self_is_zero = self.is_nonzero().not();
        let self_nz = Int::select(self, &Int::ONE, self_is_zero)
            .to_nz()
            .expect("self is non zero by construction");
        let rhs_is_zero = rhs.is_nonzero().not();
        let rhs_nz = Int::select(rhs, &Int::ONE, rhs_is_zero)
            .to_nz()
            .expect("rhs is non zero by construction");

        let NonZeroIntXgcdOutput {
            gcd,
            mut x,
            mut y,
            mut lhs_on_gcd,
            mut rhs_on_gcd,
        } = self_nz.binxgcd(&rhs_nz);

        // Correct the gcd in case self and/or rhs was zero
        let mut gcd = *gcd.as_ref();
        gcd = Uint::select(&gcd, &rhs.abs(), self_is_zero);
        gcd = Uint::select(&gcd, &self.abs(), rhs_is_zero);

        // Correct the Bézout coefficients in case self and/or rhs was zero.
        let signum_self = Int::new_from_abs_sign(Uint::ONE, self.is_negative()).expect("+/- 1");
        let signum_rhs = Int::new_from_abs_sign(Uint::ONE, rhs.is_negative()).expect("+/- 1");
        x = Int::select(&x, &Int::ZERO, self_is_zero);
        y = Int::select(&y, &signum_rhs, self_is_zero);
        x = Int::select(&x, &signum_self, rhs_is_zero);
        y = Int::select(&y, &Int::ZERO, rhs_is_zero);

        // Correct the quotients in case self and/or rhs was zero.
        lhs_on_gcd = Int::select(&lhs_on_gcd, &signum_self, rhs_is_zero);
        lhs_on_gcd = Int::select(&lhs_on_gcd, &Int::ZERO, self_is_zero);
        rhs_on_gcd = Int::select(&rhs_on_gcd, &signum_rhs, self_is_zero);
        rhs_on_gcd = Int::select(&rhs_on_gcd, &Int::ZERO, rhs_is_zero);

        IntXgcdOutput {
            gcd,
            x,
            y,
            lhs_on_gcd,
            rhs_on_gcd,
        }
    }
}

impl<const LIMBS: usize> NonZero<Int<LIMBS>> {
    /// Compute the gcd of `self` and `rhs` leveraging the Binary GCD algorithm.
    pub const fn bingcd(&self, rhs: &Self) -> NonZero<Uint<LIMBS>> {
        self.abs().bingcd(&rhs.as_ref().abs())
    }

    /// Compute the gcd of `self` and `rhs` leveraging the Binary GCD algorithm.
    ///
    /// Executes in variable time w.r.t. all input parameters.
    pub const fn bingcd_vartime(&self, rhs: &Self) -> NonZeroUint<LIMBS> {
        self.abs().bingcd_vartime(rhs.abs().as_ref())
    }

    /// Execute the Binary Extended GCD algorithm.
    ///
    /// Given `(self, rhs)`, computes `(g, x, y)` s.t. `self * x + rhs * y = g = gcd(self, rhs)`.
    pub const fn binxgcd(&self, rhs: &Self) -> NonZeroIntXgcdOutput<LIMBS> {
        let (mut lhs, mut rhs) = (*self.as_ref(), *rhs.as_ref());

        // Leverage the property that gcd(2^k * a, 2^k *b) = 2^k * gcd(a, b)
        let i = lhs.0.trailing_zeros();
        let j = rhs.0.trailing_zeros();
        let k = u32_min(i, j);
        lhs = lhs.shr(k);
        rhs = rhs.shr(k);

        // Note: at this point, either lhs or rhs is odd (or both).
        // Swap to make sure lhs is odd.
        let swap = ConstChoice::from_u32_lt(j, i);
        Int::conditional_swap(&mut lhs, &mut rhs, swap);
        let lhs = lhs.to_odd().expect("odd by construction");
        let rhs = rhs.to_nz().expect("non-zero by construction");

        let OddIntXgcdOutput {
            gcd,
            mut x,
            mut y,
            mut lhs_on_gcd,
            mut rhs_on_gcd,
        } = lhs.binxgcd(&rhs);

        // Account for the parameter swap
        Int::conditional_swap(&mut x, &mut y, swap);
        Int::conditional_swap(&mut lhs_on_gcd, &mut rhs_on_gcd, swap);

        // Reintroduce the factor 2^k to the gcd.
        let gcd = gcd
            .as_ref()
            .shl(k)
            .to_nz()
            .expect("is non-zero by construction");

        NonZeroIntXgcdOutput {
            gcd,
            x,
            y,
            lhs_on_gcd,
            rhs_on_gcd,
        }
    }
}

impl<const LIMBS: usize> Odd<Int<LIMBS>> {
    /// Compute the gcd of `self` and `rhs` leveraging the Binary GCD algorithm.
    pub const fn bingcd(&self, rhs: &Self) -> Odd<Uint<LIMBS>> {
        self.abs().bingcd(&rhs.as_ref().abs())
    }

    /// Compute the gcd of `self` and `rhs` leveraging the Binary GCD algorithm.
    ///
    /// Executes in variable time w.r.t. all input parameters.
    pub const fn bingcd_vartime(&self, rhs: &Self) -> OddUint<LIMBS> {
        self.abs().bingcd_vartime(rhs.abs().as_ref())
    }

    /// Execute the Binary Extended GCD algorithm.
    ///
    /// Given `(self, rhs)`, computes `(g, x, y)` s.t. `self * x + rhs * y = g = gcd(self, rhs)`.
    pub const fn binxgcd(&self, rhs: &NonZero<Int<LIMBS>>) -> OddIntXgcdOutput<LIMBS> {
        let (abs_lhs, sgn_lhs) = self.abs_sign();
        let (abs_rhs, sgn_rhs) = rhs.abs_sign();

        let OddUintXgcdOutput {
            gcd,
            mut x,
            mut y,
            lhs_on_gcd: abs_lhs_on_gcd,
            rhs_on_gcd: abs_rhs_on_gcd,
        } = OddUintXgcdOutput::from_pattern_output(abs_lhs.binxgcd_nz(&abs_rhs));

        x = x.wrapping_neg_if(sgn_lhs);
        y = y.wrapping_neg_if(sgn_rhs);
        let lhs_on_gcd = Int::new_from_abs_sign(abs_lhs_on_gcd, sgn_lhs).expect("no overflow");
        let rhs_on_gcd = Int::new_from_abs_sign(abs_rhs_on_gcd, sgn_rhs).expect("no overflow");

        OddIntXgcdOutput {
            gcd,
            x,
            y,
            lhs_on_gcd,
            rhs_on_gcd,
        }
    }
}

/// Output of the Binary XGCD algorithm applied to two [Int]s.
pub type IntXgcdOutput<const LIMBS: usize> = XgcdOutput<LIMBS, Uint<LIMBS>>;

/// Output of the Binary XGCD algorithm applied to two [`NonZero<Int<LIMBS>>`]s.
pub type NonZeroIntXgcdOutput<const LIMBS: usize> = XgcdOutput<LIMBS, NonZeroUint<LIMBS>>;

/// Output of the Binary XGCD algorithm applied to two [`Odd<Int<LIMBS>>`]s.
pub type OddIntXgcdOutput<const LIMBS: usize> = XgcdOutput<LIMBS, OddUint<LIMBS>>;

#[derive(Debug, Copy, Clone)]
pub struct XgcdOutput<const LIMBS: usize, T: Copy> {
    pub gcd: T,
    pub x: Int<LIMBS>,
    pub y: Int<LIMBS>,
    pub lhs_on_gcd: Int<LIMBS>,
    pub rhs_on_gcd: Int<LIMBS>,
}

impl<const LIMBS: usize, T: Copy> XgcdOutput<LIMBS, T> {
    /// Return the `gcd`.
    pub fn gcd(&self) -> T {
        self.gcd
    }

    /// Return the quotients `lhs.gcd` and `rhs/gcd`.
    pub fn quotients(&self) -> (Int<LIMBS>, Int<LIMBS>) {
        (self.lhs_on_gcd, self.rhs_on_gcd)
    }

    /// Return the Bézout coefficients `x` and `y` s.t. `lhs * x + rhs * y = gcd`.
    pub fn bezout_coefficients(&self) -> (Int<LIMBS>, Int<LIMBS>) {
        (self.x, self.y)
    }
}

impl<const LIMBS: usize> Gcd for Int<LIMBS> {
    type Output = Uint<LIMBS>;

    fn gcd(&self, rhs: &Self) -> Self::Output {
        self.bingcd(rhs)
    }

    fn gcd_vartime(&self, rhs: &Self) -> Self::Output {
        self.bingcd_vartime(rhs)
    }
}

impl<const LIMBS: usize> Gcd for NonZeroInt<LIMBS> {
    type Output = NonZeroUint<LIMBS>;

    fn gcd(&self, rhs: &Self) -> Self::Output {
        self.bingcd(rhs)
    }

    fn gcd_vartime(&self, rhs: &Self) -> Self::Output {
        self.bingcd_vartime(rhs)
    }
}

impl<const LIMBS: usize> Gcd for OddInt<LIMBS> {
    type Output = OddUint<LIMBS>;

    fn gcd(&self, rhs: &Self) -> Self::Output {
        self.bingcd(rhs)
    }

    fn gcd_vartime(&self, rhs: &Self) -> Self::Output {
        self.bingcd_vartime(rhs)
    }
}

impl<const LIMBS: usize> Gcd<Uint<LIMBS>> for Int<LIMBS> {
    type Output = Uint<LIMBS>;

    fn gcd(&self, rhs: &Uint<LIMBS>) -> Self::Output {
        self.abs().bingcd(rhs)
    }

    fn gcd_vartime(&self, rhs: &Uint<LIMBS>) -> Self::Output {
        self.abs().bingcd_vartime(rhs)
    }
}

impl<const LIMBS: usize> Gcd<NonZeroUint<LIMBS>> for NonZeroInt<LIMBS> {
    type Output = NonZeroUint<LIMBS>;

    fn gcd(&self, rhs: &NonZeroUint<LIMBS>) -> Self::Output {
        self.abs().bingcd(rhs)
    }

    fn gcd_vartime(&self, rhs: &NonZeroUint<LIMBS>) -> Self::Output {
        self.abs().bingcd_vartime(rhs)
    }
}

impl<const LIMBS: usize> Gcd<OddUint<LIMBS>> for OddInt<LIMBS> {
    type Output = OddUint<LIMBS>;

    fn gcd(&self, rhs: &OddUint<LIMBS>) -> Self::Output {
        self.abs().bingcd(rhs)
    }

    fn gcd_vartime(&self, rhs: &OddUint<LIMBS>) -> Self::Output {
        self.abs().bingcd_vartime(rhs)
    }
}

impl<const LIMBS: usize> Xgcd for Int<LIMBS> {
    type Output = IntXgcdOutput<LIMBS>;

    fn xgcd(&self, rhs: &Int<LIMBS>) -> Self::Output {
        self.binxgcd(rhs)
    }

    fn xgcd_vartime(&self, rhs: &Int<LIMBS>) -> Self::Output {
        // TODO(#853): implement vartime
        self.binxgcd(rhs)
    }
}

impl<const LIMBS: usize> Xgcd for NonZeroInt<LIMBS> {
    type Output = NonZeroIntXgcdOutput<LIMBS>;

    fn xgcd(&self, rhs: &NonZeroInt<LIMBS>) -> Self::Output {
        self.binxgcd(rhs)
    }

    fn xgcd_vartime(&self, rhs: &NonZeroInt<LIMBS>) -> Self::Output {
        // TODO(#853): implement vartime
        self.binxgcd(rhs)
    }
}

impl<const LIMBS: usize> Xgcd for OddInt<LIMBS> {
    type Output = OddIntXgcdOutput<LIMBS>;

    fn xgcd(&self, rhs: &OddInt<LIMBS>) -> Self::Output {
        self.binxgcd(rhs.as_nz_ref())
    }

    fn xgcd_vartime(&self, rhs: &OddInt<LIMBS>) -> Self::Output {
        // TODO(#853): implement vartime
        self.binxgcd(rhs.as_nz_ref())
    }
}

#[cfg(all(test, not(miri)))]
mod tests {
    use crate::int::gcd::{IntXgcdOutput, NonZeroIntXgcdOutput, OddIntXgcdOutput};
    use crate::{ConcatMixed, Int, Uint};
    use num_traits::Zero;

    impl<const LIMBS: usize> From<NonZeroIntXgcdOutput<LIMBS>> for IntXgcdOutput<LIMBS> {
        fn from(value: NonZeroIntXgcdOutput<LIMBS>) -> Self {
            let NonZeroIntXgcdOutput {
                gcd,
                x,
                y,
                lhs_on_gcd,
                rhs_on_gcd,
            } = value;
            IntXgcdOutput {
                gcd: *gcd.as_ref(),
                x,
                y,
                lhs_on_gcd,
                rhs_on_gcd,
            }
        }
    }

    impl<const LIMBS: usize> From<OddIntXgcdOutput<LIMBS>> for IntXgcdOutput<LIMBS> {
        fn from(value: OddIntXgcdOutput<LIMBS>) -> Self {
            let OddIntXgcdOutput {
                gcd,
                x,
                y,
                lhs_on_gcd,
                rhs_on_gcd,
            } = value;
            IntXgcdOutput {
                gcd: *gcd.as_ref(),
                x,
                y,
                lhs_on_gcd,
                rhs_on_gcd,
            }
        }
    }

    mod bingcd {

        use crate::{I64, I128, I256, I512, I1024, I2048, I4096, Int, Uint};

        fn test<const LIMBS: usize>(lhs: Int<LIMBS>, rhs: Int<LIMBS>, target: Uint<LIMBS>) {
            assert_eq!(lhs.bingcd(&rhs), target);
            assert_eq!(lhs.bingcd_vartime(&rhs), target);
        }

        fn run_tests<const LIMBS: usize>() {
            let abs_min = *Int::MIN.as_uint();
            let max = *Int::MAX.as_uint();
            test(Int::<LIMBS>::MIN, Int::MIN, abs_min);
            test(Int::<LIMBS>::MIN, Int::MINUS_ONE, Uint::ONE);
            test(Int::<LIMBS>::MIN, Int::ZERO, abs_min);
            test(Int::<LIMBS>::MIN, Int::ONE, Uint::ONE);
            test(Int::<LIMBS>::MIN, Int::MAX, Uint::ONE);
            test(Int::<LIMBS>::MINUS_ONE, Int::MIN, Uint::ONE);
            test(Int::<LIMBS>::MINUS_ONE, Int::MINUS_ONE, Uint::ONE);
            test(Int::<LIMBS>::MINUS_ONE, Int::ZERO, Uint::ONE);
            test(Int::<LIMBS>::MINUS_ONE, Int::ONE, Uint::ONE);
            test(Int::<LIMBS>::MINUS_ONE, Int::MAX, Uint::ONE);
            test(Int::<LIMBS>::ZERO, Int::MIN, abs_min);
            test(Int::<LIMBS>::ZERO, Int::MINUS_ONE, Uint::ONE);
            test(Int::<LIMBS>::ZERO, Int::ZERO, Uint::ZERO);
            test(Int::<LIMBS>::ZERO, Int::ONE, Uint::ONE);
            test(Int::<LIMBS>::ZERO, Int::MAX, max);
            test(Int::<LIMBS>::ONE, Int::MIN, Uint::ONE);
            test(Int::<LIMBS>::ONE, Int::MINUS_ONE, Uint::ONE);
            test(Int::<LIMBS>::ONE, Int::ZERO, Uint::ONE);
            test(Int::<LIMBS>::ONE, Int::ONE, Uint::ONE);
            test(Int::<LIMBS>::ONE, Int::MAX, Uint::ONE);
            test(Int::<LIMBS>::MAX, Int::MIN, Uint::ONE);
            test(Int::<LIMBS>::MAX, Int::MINUS_ONE, Uint::ONE);
            test(Int::<LIMBS>::MAX, Int::ZERO, max);
            test(Int::<LIMBS>::MAX, Int::ONE, Uint::ONE);
            test(Int::<LIMBS>::MAX, Int::MAX, max);
        }

        #[test]
        fn bingcd() {
            run_tests::<{ I64::LIMBS }>();
            run_tests::<{ I128::LIMBS }>();
            run_tests::<{ I256::LIMBS }>();
            run_tests::<{ I512::LIMBS }>();
            run_tests::<{ I1024::LIMBS }>();
            run_tests::<{ I2048::LIMBS }>();
            run_tests::<{ I4096::LIMBS }>();
        }
    }

    fn binxgcd_test<const LIMBS: usize, const DOUBLE: usize>(
        lhs: Int<LIMBS>,
        rhs: Int<LIMBS>,
        output: IntXgcdOutput<LIMBS>,
    ) where
        Uint<LIMBS>: ConcatMixed<Uint<LIMBS>, MixedOutput = Uint<DOUBLE>>,
    {
        let gcd = lhs.bingcd(&rhs);
        assert_eq!(gcd, output.gcd);

        // Test quotients
        let (lhs_on_gcd, rhs_on_gcd) = output.quotients();
        if gcd.is_zero() {
            assert_eq!(lhs_on_gcd, Int::ZERO);
            assert_eq!(rhs_on_gcd, Int::ZERO);
        } else {
            assert_eq!(lhs_on_gcd, lhs.div_uint(&gcd.to_nz().unwrap()));
            assert_eq!(rhs_on_gcd, rhs.div_uint(&gcd.to_nz().unwrap()));
        }

        // Test the Bezout coefficients on minimality
        let (x, y) = output.bezout_coefficients();
        assert!(x.abs() <= rhs_on_gcd.abs() || rhs_on_gcd.is_zero());
        assert!(y.abs() <= lhs_on_gcd.abs() || lhs_on_gcd.is_zero());
        if lhs.abs() != rhs.abs() {
            assert!(x.abs() <= rhs_on_gcd.abs().shr(1) || rhs_on_gcd.is_zero());
            assert!(y.abs() <= lhs_on_gcd.abs().shr(1) || lhs_on_gcd.is_zero());
        }

        // Test the Bezout coefficients for correctness
        assert_eq!(
            x.concatenating_mul(&lhs)
                .wrapping_add(&y.concatenating_mul(&rhs)),
            *gcd.resize().as_int()
        );
    }

    mod test_int_binxgcd {
        use crate::int::gcd::tests::binxgcd_test;
        use crate::{
            ConcatMixed, Gcd, Int, U64, U128, U192, U256, U384, U512, U768, U1024, U2048, U4096,
            U8192, Uint,
        };

        fn test<const LIMBS: usize, const DOUBLE: usize>(lhs: Int<LIMBS>, rhs: Int<LIMBS>)
        where
            Uint<LIMBS>: ConcatMixed<Uint<LIMBS>, MixedOutput = Uint<DOUBLE>>,
            Int<LIMBS>: Gcd<Output = Uint<LIMBS>>,
        {
            binxgcd_test(lhs, rhs, lhs.binxgcd(&rhs))
        }

        fn run_tests<const LIMBS: usize, const DOUBLE: usize>()
        where
            Uint<LIMBS>: ConcatMixed<Uint<LIMBS>, MixedOutput = Uint<DOUBLE>>,
            Int<LIMBS>: Gcd<Output = Uint<LIMBS>>,
        {
            test(Int::MIN, Int::MIN);
            test(Int::MIN, Int::MINUS_ONE);
            test(Int::MIN, Int::ZERO);
            test(Int::MIN, Int::ONE);
            test(Int::MIN, Int::MAX);
            test(Int::ONE, Int::MIN);
            test(Int::ONE, Int::MINUS_ONE);
            test(Int::ONE, Int::ZERO);
            test(Int::ONE, Int::ONE);
            test(Int::ONE, Int::MAX);
            test(Int::ZERO, Int::MIN);
            test(Int::ZERO, Int::MINUS_ONE);
            test(Int::ZERO, Int::ZERO);
            test(Int::ZERO, Int::ONE);
            test(Int::ZERO, Int::MAX);
            test(Int::ONE, Int::MIN);
            test(Int::ONE, Int::MINUS_ONE);
            test(Int::ONE, Int::ZERO);
            test(Int::ONE, Int::ONE);
            test(Int::ONE, Int::MAX);
            test(Int::MAX, Int::MIN);
            test(Int::MAX, Int::MINUS_ONE);
            test(Int::MAX, Int::ZERO);
            test(Int::MAX, Int::ONE);
            test(Int::MAX, Int::MAX);
        }

        #[test]
        fn binxgcd() {
            run_tests::<{ U64::LIMBS }, { U128::LIMBS }>();
            run_tests::<{ U128::LIMBS }, { U256::LIMBS }>();
            run_tests::<{ U192::LIMBS }, { U384::LIMBS }>();
            run_tests::<{ U256::LIMBS }, { U512::LIMBS }>();
            run_tests::<{ U384::LIMBS }, { U768::LIMBS }>();
            run_tests::<{ U512::LIMBS }, { U1024::LIMBS }>();
            run_tests::<{ U1024::LIMBS }, { U2048::LIMBS }>();
            run_tests::<{ U2048::LIMBS }, { U4096::LIMBS }>();
            run_tests::<{ U4096::LIMBS }, { U8192::LIMBS }>();
        }
    }

    mod test_nonzero_int_binxgcd {
        use crate::int::gcd::tests::binxgcd_test;
        use crate::{
            ConcatMixed, Int, U64, U128, U192, U256, U384, U512, U768, U1024, U2048, U4096, U8192,
            Uint,
        };

        fn test<const LIMBS: usize, const DOUBLE: usize>(lhs: Int<LIMBS>, rhs: Int<LIMBS>)
        where
            Uint<LIMBS>: ConcatMixed<Uint<LIMBS>, MixedOutput = Uint<DOUBLE>>,
        {
            let output = lhs.to_nz().unwrap().binxgcd(&rhs.to_nz().unwrap());
            binxgcd_test(lhs, rhs, output.into());
        }

        fn run_tests<const LIMBS: usize, const DOUBLE: usize>()
        where
            Uint<LIMBS>: ConcatMixed<Uint<LIMBS>, MixedOutput = Uint<DOUBLE>>,
        {
            test(Int::MIN, Int::MIN);
            test(Int::MIN, Int::MINUS_ONE);
            test(Int::MIN, Int::ONE);
            test(Int::MIN, Int::MAX);
            test(Int::MINUS_ONE, Int::MIN);
            test(Int::MINUS_ONE, Int::MINUS_ONE);
            test(Int::MINUS_ONE, Int::ONE);
            test(Int::MINUS_ONE, Int::MAX);
            test(Int::ONE, Int::MIN);
            test(Int::ONE, Int::MINUS_ONE);
            test(Int::ONE, Int::ONE);
            test(Int::ONE, Int::MAX);
            test(Int::MAX, Int::MIN);
            test(Int::MAX, Int::MINUS_ONE);
            test(Int::MAX, Int::ONE);
            test(Int::MAX, Int::MAX);
        }

        #[test]
        fn binxgcd() {
            run_tests::<{ U64::LIMBS }, { U128::LIMBS }>();
            run_tests::<{ U128::LIMBS }, { U256::LIMBS }>();
            run_tests::<{ U192::LIMBS }, { U384::LIMBS }>();
            run_tests::<{ U256::LIMBS }, { U512::LIMBS }>();
            run_tests::<{ U384::LIMBS }, { U768::LIMBS }>();
            run_tests::<{ U512::LIMBS }, { U1024::LIMBS }>();
            run_tests::<{ U1024::LIMBS }, { U2048::LIMBS }>();
            run_tests::<{ U2048::LIMBS }, { U4096::LIMBS }>();
            run_tests::<{ U4096::LIMBS }, { U8192::LIMBS }>();
        }
    }

    mod test_odd_int_binxgcd {
        use crate::int::gcd::tests::binxgcd_test;
        use crate::{
            ConcatMixed, Int, U64, U128, U192, U256, U384, U512, U768, U1024, U2048, U4096, U8192,
            Uint,
        };

        fn test<const LIMBS: usize, const DOUBLE: usize>(lhs: Int<LIMBS>, rhs: Int<LIMBS>)
        where
            Uint<LIMBS>: ConcatMixed<Uint<LIMBS>, MixedOutput = Uint<DOUBLE>>,
        {
            let output = lhs.to_odd().unwrap().binxgcd(&rhs.to_nz().unwrap());
            binxgcd_test(lhs, rhs, output.into());
        }

        fn run_tests<const LIMBS: usize, const DOUBLE: usize>()
        where
            Uint<LIMBS>: ConcatMixed<Uint<LIMBS>, MixedOutput = Uint<DOUBLE>>,
        {
            let neg_max = Int::MAX.wrapping_neg();
            test(neg_max, neg_max);
            test(neg_max, Int::MINUS_ONE);
            test(neg_max, Int::ONE);
            test(neg_max, Int::MAX);
            test(Int::ONE, neg_max);
            test(Int::ONE, Int::MINUS_ONE);
            test(Int::ONE, Int::ONE);
            test(Int::ONE, Int::MAX);
            test(Int::MAX, neg_max);
            test(Int::MAX, Int::MINUS_ONE);
            test(Int::MAX, Int::ONE);
            test(Int::MAX, Int::MAX);
        }

        #[test]
        fn binxgcd() {
            run_tests::<{ U64::LIMBS }, { U128::LIMBS }>();
            run_tests::<{ U128::LIMBS }, { U256::LIMBS }>();
            run_tests::<{ U192::LIMBS }, { U384::LIMBS }>();
            run_tests::<{ U256::LIMBS }, { U512::LIMBS }>();
            run_tests::<{ U384::LIMBS }, { U768::LIMBS }>();
            run_tests::<{ U512::LIMBS }, { U1024::LIMBS }>();
            run_tests::<{ U1024::LIMBS }, { U2048::LIMBS }>();
            run_tests::<{ U2048::LIMBS }, { U4096::LIMBS }>();
            run_tests::<{ U4096::LIMBS }, { U8192::LIMBS }>();
        }
    }

    mod traits {
        use crate::{Gcd, I256, U256};

        #[test]
        fn gcd_always_positive() {
            // Two numbers with a shared factor of 61
            let f = I256::from(59i32 * 61);
            let g = I256::from(61i32 * 71);

            assert_eq!(U256::from(61u32), f.gcd(&g));
            assert_eq!(U256::from(61u32), f.wrapping_neg().gcd(&g));
            assert_eq!(U256::from(61u32), f.gcd(&g.wrapping_neg()));
            assert_eq!(U256::from(61u32), f.wrapping_neg().gcd(&g.wrapping_neg()));
        }

        #[test]
        fn gcd_int_uint() {
            // Two numbers with a shared factor of 61
            let f = I256::from(59i32 * 61);
            let g = U256::from(61u32 * 71);

            assert_eq!(U256::from(61u32), f.gcd(&g));
            assert_eq!(U256::from(61u32), f.wrapping_neg().gcd(&g));
        }
    }
}
