//! This module implements (a constant variant of) the Optimized Extended Binary GCD algorithm,
//! which is described by Pornin in "Optimized Binary GCD for Modular Inversion".
//! Ref: <https://eprint.iacr.org/2020/972.pdf>

use crate::modular::bingcd::OddUintBinxgcdOutput;
use crate::modular::bingcd::tools::const_min;
use crate::{ConstChoice, Int, NonZero, Odd, Uint};

#[derive(Debug)]
pub struct BaseIntBinxgcdOutput<T: Copy, const LIMBS: usize> {
    pub gcd: T,
    pub x: Int<LIMBS>,
    pub y: Int<LIMBS>,
    pub lhs_on_gcd: Int<LIMBS>,
    pub rhs_on_gcd: Int<LIMBS>,
}

/// Output of the Binary XGCD algorithm applied to two [Int]s.
pub type IntBinxgcdOutput<const LIMBS: usize> = BaseIntBinxgcdOutput<Uint<LIMBS>, LIMBS>;

/// Output of the Binary XGCD algorithm applied to two [`NonZero<Int<LIMBS>>`]s.
pub type NonZeroIntBinxgcdOutput<const LIMBS: usize> =
    BaseIntBinxgcdOutput<NonZero<Uint<LIMBS>>, LIMBS>;

/// Output of the Binary XGCD algorithm applied to two [`Odd<Int<LIMBS>>`]s.
pub type OddIntBinxgcdOutput<const LIMBS: usize> = BaseIntBinxgcdOutput<Odd<Uint<LIMBS>>, LIMBS>;

impl<T: Copy, const LIMBS: usize> BaseIntBinxgcdOutput<T, LIMBS> {
    /// Return the quotients `lhs.gcd` and `rhs/gcd`.
    pub fn quotients(&self) -> (Int<LIMBS>, Int<LIMBS>) {
        (self.lhs_on_gcd, self.rhs_on_gcd)
    }

    /// Provide mutable access to the quotients `lhs.gcd` and `rhs/gcd`.
    pub fn quotients_as_mut(&mut self) -> (&mut Int<LIMBS>, &mut Int<LIMBS>) {
        (&mut self.lhs_on_gcd, &mut self.rhs_on_gcd)
    }

    /// Return the Bézout coefficients `x` and `y` s.t. `lhs * x + rhs * y = gcd`.
    pub fn bezout_coefficients(&self) -> (Int<LIMBS>, Int<LIMBS>) {
        (self.x, self.y)
    }

    /// Provide mutable access to the Bézout coefficients.
    pub fn bezout_coefficients_as_mut(&mut self) -> (&mut Int<LIMBS>, &mut Int<LIMBS>) {
        (&mut self.x, &mut self.y)
    }
}

impl<const LIMBS: usize> Int<LIMBS> {
    /// Compute the gcd of `self` and `rhs` leveraging the Binary GCD algorithm.
    pub fn bingcd(&self, rhs: &Self) -> Uint<LIMBS> {
        self.abs().bingcd(&rhs.abs())
    }

    /// Executes the Binary Extended GCD algorithm.
    ///
    /// Given `(self, rhs)`, computes `(g, x, y)`, s.t. `self * x + rhs * y = g = gcd(self, rhs)`.
    pub fn binxgcd(&self, rhs: &Self) -> IntBinxgcdOutput<LIMBS> {
        // Make sure `self` and `rhs` are nonzero.
        let self_is_zero = self.is_nonzero().not();
        let self_nz = Int::select(self, &Int::ONE, self_is_zero)
            .to_nz()
            .expect("self is non zero by construction");
        let rhs_is_zero = rhs.is_nonzero().not();
        let rhs_nz = Int::select(rhs, &Int::ONE, rhs_is_zero)
            .to_nz()
            .expect("rhs is non zero by construction");

        let NonZeroIntBinxgcdOutput {
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

        IntBinxgcdOutput {
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
    pub fn bingcd(&self, rhs: &Self) -> NonZero<Uint<LIMBS>> {
        self.abs().bingcd(&rhs.as_ref().abs())
    }

    /// Execute the Binary Extended GCD algorithm.
    ///
    /// Given `(self, rhs)`, computes `(g, x, y)` s.t. `self * x + rhs * y = g = gcd(self, rhs)`.
    pub fn binxgcd(&self, rhs: &Self) -> NonZeroIntBinxgcdOutput<LIMBS> {
        let (mut lhs, mut rhs) = (*self.as_ref(), *rhs.as_ref());

        // Leverage the property that gcd(2^k * a, 2^k *b) = 2^k * gcd(a, b)
        let i = lhs.0.trailing_zeros();
        let j = rhs.0.trailing_zeros();
        let k = const_min(i, j);
        lhs = lhs.shr(k);
        rhs = rhs.shr(k);

        // Note: at this point, either lhs or rhs is odd (or both).
        // Swap to make sure lhs is odd.
        let swap = ConstChoice::from_u32_lt(j, i);
        Int::conditional_swap(&mut lhs, &mut rhs, swap);
        let lhs = lhs.to_odd().expect("odd by construction");

        let rhs = rhs.to_nz().expect("non-zero by construction");
        let OddIntBinxgcdOutput {
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

        NonZeroIntBinxgcdOutput {
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
    pub fn bingcd(&self, rhs: &Self) -> Odd<Uint<LIMBS>> {
        self.abs().bingcd(&rhs.as_ref().abs())
    }

    /// Execute the Binary Extended GCD algorithm.
    ///
    /// Given `(self, rhs)`, computes `(g, x, y)` s.t. `self * x + rhs * y = g = gcd(self, rhs)`.
    pub fn binxgcd(&self, rhs: &NonZero<Int<LIMBS>>) -> OddIntBinxgcdOutput<LIMBS> {
        let (abs_lhs, sgn_lhs) = self.abs_sign();
        let (abs_rhs, sgn_rhs) = rhs.abs_sign();

        let OddUintBinxgcdOutput {
            gcd,
            mut x,
            mut y,
            lhs_on_gcd: abs_lhs_on_gcd,
            rhs_on_gcd: abs_rhs_on_gcd,
        } = abs_lhs.binxgcd_nz(&abs_rhs);

        x = x.wrapping_neg_if(sgn_lhs);
        y = y.wrapping_neg_if(sgn_rhs);
        let lhs_on_gcd = Int::new_from_abs_sign(abs_lhs_on_gcd, sgn_lhs).expect("no overflow");
        let rhs_on_gcd = Int::new_from_abs_sign(abs_rhs_on_gcd, sgn_rhs).expect("no overflow");

        OddIntBinxgcdOutput {
            gcd,
            x,
            y,
            lhs_on_gcd,
            rhs_on_gcd,
        }
    }
}

#[cfg(all(test, not(miri)))]
mod test {
    use crate::int::bingcd::{IntBinxgcdOutput, NonZeroIntBinxgcdOutput, OddIntBinxgcdOutput};
    use crate::{ConcatMixed, Int, Uint};
    use num_traits::Zero;

    #[cfg(feature = "rand_core")]
    use rand_chacha::ChaChaRng;
    #[cfg(feature = "rand_core")]
    use rand_core::SeedableRng;

    impl<const LIMBS: usize> From<NonZeroIntBinxgcdOutput<LIMBS>> for IntBinxgcdOutput<LIMBS> {
        fn from(value: NonZeroIntBinxgcdOutput<LIMBS>) -> Self {
            let NonZeroIntBinxgcdOutput {
                gcd,
                x,
                y,
                lhs_on_gcd,
                rhs_on_gcd,
            } = value;
            IntBinxgcdOutput {
                gcd: *gcd.as_ref(),
                x,
                y,
                lhs_on_gcd,
                rhs_on_gcd,
            }
        }
    }

    impl<const LIMBS: usize> From<OddIntBinxgcdOutput<LIMBS>> for IntBinxgcdOutput<LIMBS> {
        fn from(value: OddIntBinxgcdOutput<LIMBS>) -> Self {
            let OddIntBinxgcdOutput {
                gcd,
                x,
                y,
                lhs_on_gcd,
                rhs_on_gcd,
            } = value;
            IntBinxgcdOutput {
                gcd: *gcd.as_ref(),
                x,
                y,
                lhs_on_gcd,
                rhs_on_gcd,
            }
        }
    }

    #[cfg(feature = "rand_core")]
    pub(crate) fn make_rng() -> ChaChaRng {
        ChaChaRng::from_seed([0; 32])
    }

    fn binxgcd_test<const LIMBS: usize, const DOUBLE: usize>(
        lhs: Int<LIMBS>,
        rhs: Int<LIMBS>,
        output: IntBinxgcdOutput<LIMBS>,
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
            x.widening_mul(&lhs).wrapping_add(&y.widening_mul(&rhs)),
            gcd.resize().as_int()
        );
    }

    mod test_int_binxgcd {
        use crate::int::bingcd::test::binxgcd_test;
        use crate::{
            ConcatMixed, Gcd, Int, U64, U128, U192, U256, U384, U512, U768, U1024, U2048, U4096,
            U8192, Uint,
        };

        #[cfg(feature = "rand_core")]
        use crate::Random;
        #[cfg(feature = "rand_core")]
        use crate::int::bingcd::test::make_rng;

        fn int_binxgcd_test<const LIMBS: usize, const DOUBLE: usize>(
            lhs: Int<LIMBS>,
            rhs: Int<LIMBS>,
        ) where
            Uint<LIMBS>: ConcatMixed<Uint<LIMBS>, MixedOutput = Uint<DOUBLE>>,
            Int<LIMBS>: Gcd<Output = Uint<LIMBS>>,
        {
            binxgcd_test(lhs, rhs, lhs.binxgcd(&rhs))
        }

        #[cfg(feature = "rand_core")]
        fn int_binxgcd_randomized_tests<const LIMBS: usize, const DOUBLE: usize>(iterations: u32)
        where
            Uint<LIMBS>: ConcatMixed<Uint<LIMBS>, MixedOutput = Uint<DOUBLE>>,
            Int<LIMBS>: Gcd<Output = Uint<LIMBS>>,
        {
            let mut rng = make_rng();
            for _ in 0..iterations {
                let x = Int::random(&mut rng);
                let y = Int::random(&mut rng);
                int_binxgcd_test(x, y);
            }
        }

        fn int_binxgcd_tests<const LIMBS: usize, const DOUBLE: usize>()
        where
            Uint<LIMBS>: ConcatMixed<Uint<LIMBS>, MixedOutput = Uint<DOUBLE>>,
            Int<LIMBS>: Gcd<Output = Uint<LIMBS>>,
        {
            int_binxgcd_test(Int::MIN, Int::MIN);
            int_binxgcd_test(Int::MIN, Int::MINUS_ONE);
            int_binxgcd_test(Int::MIN, Int::ZERO);
            int_binxgcd_test(Int::MIN, Int::ONE);
            int_binxgcd_test(Int::MIN, Int::MAX);
            int_binxgcd_test(Int::ONE, Int::MIN);
            int_binxgcd_test(Int::ONE, Int::MINUS_ONE);
            int_binxgcd_test(Int::ONE, Int::ZERO);
            int_binxgcd_test(Int::ONE, Int::ONE);
            int_binxgcd_test(Int::ONE, Int::MAX);
            int_binxgcd_test(Int::ZERO, Int::MIN);
            int_binxgcd_test(Int::ZERO, Int::MINUS_ONE);
            int_binxgcd_test(Int::ZERO, Int::ZERO);
            int_binxgcd_test(Int::ZERO, Int::ONE);
            int_binxgcd_test(Int::ZERO, Int::MAX);
            int_binxgcd_test(Int::ONE, Int::MIN);
            int_binxgcd_test(Int::ONE, Int::MINUS_ONE);
            int_binxgcd_test(Int::ONE, Int::ZERO);
            int_binxgcd_test(Int::ONE, Int::ONE);
            int_binxgcd_test(Int::ONE, Int::MAX);
            int_binxgcd_test(Int::MAX, Int::MIN);
            int_binxgcd_test(Int::MAX, Int::MINUS_ONE);
            int_binxgcd_test(Int::MAX, Int::ZERO);
            int_binxgcd_test(Int::MAX, Int::ONE);
            int_binxgcd_test(Int::MAX, Int::MAX);

            #[cfg(feature = "rand_core")]
            int_binxgcd_randomized_tests(100);
        }

        #[test]
        fn test_int_binxgcd() {
            int_binxgcd_tests::<{ U64::LIMBS }, { U128::LIMBS }>();
            int_binxgcd_tests::<{ U128::LIMBS }, { U256::LIMBS }>();
            int_binxgcd_tests::<{ U192::LIMBS }, { U384::LIMBS }>();
            int_binxgcd_tests::<{ U256::LIMBS }, { U512::LIMBS }>();
            int_binxgcd_tests::<{ U384::LIMBS }, { U768::LIMBS }>();
            int_binxgcd_tests::<{ U512::LIMBS }, { U1024::LIMBS }>();
            int_binxgcd_tests::<{ U1024::LIMBS }, { U2048::LIMBS }>();
            int_binxgcd_tests::<{ U2048::LIMBS }, { U4096::LIMBS }>();
            int_binxgcd_tests::<{ U4096::LIMBS }, { U8192::LIMBS }>();
        }
    }

    mod test_nonzero_int_binxgcd {
        use crate::int::bingcd::test::binxgcd_test;
        use crate::{
            ConcatMixed, Gcd, Int, U64, U128, U192, U256, U384, U512, U768, U1024, U2048, U4096,
            U8192, Uint,
        };

        #[cfg(feature = "rand_core")]
        use crate::{Random, int::bingcd::test::make_rng};

        fn nz_int_binxgcd_test<const LIMBS: usize, const DOUBLE: usize>(
            lhs: Int<LIMBS>,
            rhs: Int<LIMBS>,
        ) where
            Uint<LIMBS>: ConcatMixed<Uint<LIMBS>, MixedOutput = Uint<DOUBLE>>,
            Int<LIMBS>: Gcd<Output = Uint<LIMBS>>,
        {
            let output = lhs.to_nz().unwrap().binxgcd(&rhs.to_nz().unwrap());
            binxgcd_test(lhs, rhs, output.into());
        }

        #[cfg(feature = "rand_core")]
        fn nz_int_binxgcd_randomized_tests<const LIMBS: usize, const DOUBLE: usize>(iterations: u32)
        where
            Uint<LIMBS>: ConcatMixed<Uint<LIMBS>, MixedOutput = Uint<DOUBLE>>,
            Int<LIMBS>: Gcd<Output = Uint<LIMBS>>,
        {
            let mut rng = make_rng();
            for _ in 0..iterations {
                let x = Uint::random(&mut rng).as_int();
                let y = Uint::random(&mut rng).as_int();
                nz_int_binxgcd_test(x, y);
            }
        }

        fn nz_int_binxgcd_tests<const LIMBS: usize, const DOUBLE: usize>()
        where
            Uint<LIMBS>: ConcatMixed<Uint<LIMBS>, MixedOutput = Uint<DOUBLE>>,
            Int<LIMBS>: Gcd<Output = Uint<LIMBS>>,
        {
            nz_int_binxgcd_test(Int::MIN, Int::MIN);
            nz_int_binxgcd_test(Int::MIN, Int::MINUS_ONE);
            nz_int_binxgcd_test(Int::MIN, Int::ONE);
            nz_int_binxgcd_test(Int::MIN, Int::MAX);
            nz_int_binxgcd_test(Int::MINUS_ONE, Int::MIN);
            nz_int_binxgcd_test(Int::MINUS_ONE, Int::MINUS_ONE);
            nz_int_binxgcd_test(Int::MINUS_ONE, Int::ONE);
            nz_int_binxgcd_test(Int::MINUS_ONE, Int::MAX);
            nz_int_binxgcd_test(Int::ONE, Int::MIN);
            nz_int_binxgcd_test(Int::ONE, Int::MINUS_ONE);
            nz_int_binxgcd_test(Int::ONE, Int::ONE);
            nz_int_binxgcd_test(Int::ONE, Int::MAX);
            nz_int_binxgcd_test(Int::MAX, Int::MIN);
            nz_int_binxgcd_test(Int::MAX, Int::MINUS_ONE);
            nz_int_binxgcd_test(Int::MAX, Int::ONE);
            nz_int_binxgcd_test(Int::MAX, Int::MAX);

            #[cfg(feature = "rand_core")]
            nz_int_binxgcd_randomized_tests(100);
        }

        #[test]
        fn test_nz_int_binxgcd() {
            nz_int_binxgcd_tests::<{ U64::LIMBS }, { U128::LIMBS }>();
            nz_int_binxgcd_tests::<{ U128::LIMBS }, { U256::LIMBS }>();
            nz_int_binxgcd_tests::<{ U192::LIMBS }, { U384::LIMBS }>();
            nz_int_binxgcd_tests::<{ U256::LIMBS }, { U512::LIMBS }>();
            nz_int_binxgcd_tests::<{ U384::LIMBS }, { U768::LIMBS }>();
            nz_int_binxgcd_tests::<{ U512::LIMBS }, { U1024::LIMBS }>();
            nz_int_binxgcd_tests::<{ U1024::LIMBS }, { U2048::LIMBS }>();
            nz_int_binxgcd_tests::<{ U2048::LIMBS }, { U4096::LIMBS }>();
            nz_int_binxgcd_tests::<{ U4096::LIMBS }, { U8192::LIMBS }>();
        }
    }

    mod test_odd_int_binxgcd {
        use crate::int::bingcd::test::binxgcd_test;
        use crate::{
            ConcatMixed, Int, U64, U128, U192, U256, U384, U512, U768, U1024, U2048, U4096, U8192,
            Uint,
        };

        #[cfg(feature = "rand_core")]
        use crate::{Random, int::bingcd::test::make_rng};

        fn odd_int_binxgcd_test<const LIMBS: usize, const DOUBLE: usize>(
            lhs: Int<LIMBS>,
            rhs: Int<LIMBS>,
        ) where
            Uint<LIMBS>: ConcatMixed<Uint<LIMBS>, MixedOutput = Uint<DOUBLE>>,
        {
            let output = lhs.to_odd().unwrap().binxgcd(&rhs.to_nz().unwrap());
            binxgcd_test(lhs, rhs, output.into());
        }

        #[cfg(feature = "rand_core")]
        fn odd_int_binxgcd_randomized_tests<const LIMBS: usize, const DOUBLE: usize>(
            iterations: u32,
        ) where
            Uint<LIMBS>: ConcatMixed<Uint<LIMBS>, MixedOutput = Uint<DOUBLE>>,
        {
            let mut rng = make_rng();
            for _ in 0..iterations {
                let x = Int::<LIMBS>::random(&mut rng).bitor(&Int::ONE);
                let y = Int::<LIMBS>::random(&mut rng);
                odd_int_binxgcd_test(x, y);
            }
        }

        fn odd_int_binxgcd_tests<const LIMBS: usize, const DOUBLE: usize>()
        where
            Uint<LIMBS>: ConcatMixed<Uint<LIMBS>, MixedOutput = Uint<DOUBLE>>,
        {
            let neg_max = Int::MAX.wrapping_neg();
            odd_int_binxgcd_test(neg_max, neg_max);
            odd_int_binxgcd_test(neg_max, Int::MINUS_ONE);
            odd_int_binxgcd_test(neg_max, Int::ONE);
            odd_int_binxgcd_test(neg_max, Int::MAX);
            odd_int_binxgcd_test(Int::ONE, neg_max);
            odd_int_binxgcd_test(Int::ONE, Int::MINUS_ONE);
            odd_int_binxgcd_test(Int::ONE, Int::ONE);
            odd_int_binxgcd_test(Int::ONE, Int::MAX);
            odd_int_binxgcd_test(Int::MAX, neg_max);
            odd_int_binxgcd_test(Int::MAX, Int::MINUS_ONE);
            odd_int_binxgcd_test(Int::MAX, Int::ONE);
            odd_int_binxgcd_test(Int::MAX, Int::MAX);

            #[cfg(feature = "rand_core")]
            odd_int_binxgcd_randomized_tests(100);
        }

        #[test]
        fn test_odd_int_binxgcd() {
            odd_int_binxgcd_tests::<{ U64::LIMBS }, { U128::LIMBS }>();
            odd_int_binxgcd_tests::<{ U128::LIMBS }, { U256::LIMBS }>();
            odd_int_binxgcd_tests::<{ U192::LIMBS }, { U384::LIMBS }>();
            odd_int_binxgcd_tests::<{ U256::LIMBS }, { U512::LIMBS }>();
            odd_int_binxgcd_tests::<{ U384::LIMBS }, { U768::LIMBS }>();
            odd_int_binxgcd_tests::<{ U512::LIMBS }, { U1024::LIMBS }>();
            odd_int_binxgcd_tests::<{ U1024::LIMBS }, { U2048::LIMBS }>();
            odd_int_binxgcd_tests::<{ U2048::LIMBS }, { U4096::LIMBS }>();
            odd_int_binxgcd_tests::<{ U4096::LIMBS }, { U8192::LIMBS }>();
        }
    }
}
