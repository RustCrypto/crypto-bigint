//! This module implements Binary (Extended) GCD for [`Uint`].

use crate::const_choice::u32_min;
use crate::modular::bingcd::xgcd::PatternXgcdOutput;
use crate::{ConstChoice, Gcd, Int, NonZero, NonZeroUint, Odd, OddUint, Uint, Xgcd};

impl<const LIMBS: usize> Uint<LIMBS> {
    /// Compute the greatest common divisor of `self` and `rhs`.
    pub const fn bingcd(&self, rhs: &Self) -> Self {
        let self_is_zero = self.is_nonzero().not();
        // Note: is non-zero by construction
        let self_nz = NonZero(Uint::select(self, &Uint::ONE, self_is_zero));
        Uint::select(self_nz.bingcd(rhs).as_ref(), rhs, self_is_zero)
    }

    /// Compute the greatest common divisor of `self` and `rhs`.
    ///
    /// Executes in variable time w.r.t. all input parameters.
    pub const fn bingcd_vartime(&self, rhs: &Self) -> Self {
        let self_is_zero = self.is_nonzero().not();
        // Note: is non-zero by construction
        let self_nz = NonZero(Uint::select(self, &Uint::ONE, self_is_zero));
        Uint::select(self_nz.bingcd_vartime(rhs).as_ref(), rhs, self_is_zero)
    }

    /// Executes the Binary Extended GCD algorithm.
    ///
    /// Given `(self, rhs)`, computes `(g, x, y)`, s.t. `self * x + rhs * y = g = gcd(self, rhs)`.
    pub fn binxgcd(&self, rhs: &Self) -> UintXgcdOutput<LIMBS> {
        // Make sure `self` and `rhs` are nonzero.
        let self_is_zero = self.is_nonzero().not();
        let self_nz = NonZero(Uint::select(self, &Uint::ONE, self_is_zero));
        let rhs_is_zero = rhs.is_nonzero().not();
        let rhs_nz = NonZero(Uint::select(rhs, &Uint::ONE, rhs_is_zero));

        let NonZeroUintXgcdOutput {
            gcd,
            mut x,
            mut y,
            mut lhs_on_gcd,
            mut rhs_on_gcd,
        } = self_nz.binxgcd(&rhs_nz);

        // Correct the gcd in case self and/or rhs was zero
        let mut gcd = *gcd.as_ref();
        gcd = Uint::select(&gcd, rhs, self_is_zero);
        gcd = Uint::select(&gcd, self, rhs_is_zero);

        // Correct the Bézout coefficients in case self and/or rhs was zero.
        x = Int::select(&x, &Int::ZERO, self_is_zero);
        y = Int::select(&y, &Int::ONE, self_is_zero);
        x = Int::select(&x, &Int::ONE, rhs_is_zero);
        y = Int::select(&y, &Int::ZERO, rhs_is_zero);

        // Correct the quotients in case self and/or rhs was zero.
        lhs_on_gcd = Uint::select(&lhs_on_gcd, &Uint::ZERO, self_is_zero);
        rhs_on_gcd = Uint::select(&rhs_on_gcd, &Uint::ONE, self_is_zero);
        lhs_on_gcd = Uint::select(&lhs_on_gcd, &Uint::ONE, rhs_is_zero);
        rhs_on_gcd = Uint::select(&rhs_on_gcd, &Uint::ZERO, rhs_is_zero);

        UintXgcdOutput {
            gcd,
            x,
            y,
            lhs_on_gcd,
            rhs_on_gcd,
        }
    }
}

impl<const LIMBS: usize> NonZeroUint<LIMBS> {
    /// Compute the greatest common divisor of `self` and `rhs`.
    pub const fn bingcd(&self, rhs: &Uint<LIMBS>) -> Self {
        let lhs = self.as_ref();

        // Note the following two GCD identity rules:
        // 1) gcd(2a, 2b) = 2 · gcd(a, b), and
        // 2) gcd(a, 2b) = gcd(a, b) if a is odd.
        //
        // Combined, these rules imply that
        // 3) gcd(2^i · a, 2^j · b) = 2^k · gcd(a, b), with k = min(i, j).
        //
        // However, to save ourselves having to divide out 2^j, we also note that
        // 4) 2^k · gcd(a, b) = 2^k · gcd(a, 2^j · b)

        let i = lhs.trailing_zeros();
        let j = rhs.trailing_zeros();
        let k = u32_min(i, j);

        let odd_lhs = Odd(lhs.shr(i));
        let gcd_div_2k = odd_lhs.bingcd(rhs);
        NonZero(gcd_div_2k.as_ref().shl(k))
    }

    /// Compute the greatest common divisor of `self` and `rhs`.
    ///
    /// Executes in variable time w.r.t. all input parameters.
    pub const fn bingcd_vartime(&self, rhs: &Uint<LIMBS>) -> Self {
        let lhs = self.as_ref();

        let i = lhs.trailing_zeros_vartime();
        let j = rhs.trailing_zeros_vartime();
        let k = u32_min(i, j);

        let odd_lhs = Odd(lhs.shr_vartime(i));
        let gcd_div_2k = odd_lhs.bingcd_vartime(rhs);
        NonZero(gcd_div_2k.as_ref().shl_vartime(k))
    }

    /// Execute the Binary Extended GCD algorithm.
    ///
    /// Given `(self, rhs)`, computes `(g, x, y)` s.t. `self * x + rhs * y = g = gcd(self, rhs)`.
    pub fn binxgcd(&self, rhs: &Self) -> NonZeroUintXgcdOutput<LIMBS> {
        let (mut lhs, mut rhs) = (*self.as_ref(), *rhs.as_ref());

        // Observe that gcd(2^i · a, 2^j · b) = 2^k * gcd(2^(i-k)·a, 2^(j-k)·b), with k = min(i,j).
        let i = lhs.trailing_zeros();
        let j = rhs.trailing_zeros();
        let k = u32_min(i, j);
        lhs = lhs.shr(k);
        rhs = rhs.shr(k);

        // At this point, either lhs or rhs is odd (or both); swap to make sure lhs is odd.
        let swap = ConstChoice::from_u32_lt(j, i);
        Uint::conditional_swap(&mut lhs, &mut rhs, swap);
        let lhs = lhs.to_odd().expect("odd by construction");
        let rhs = rhs.to_nz().expect("non-zero by construction");

        let OddUintXgcdOutput {
            gcd,
            mut x,
            mut y,
            mut lhs_on_gcd,
            mut rhs_on_gcd,
        } = OddUintXgcdOutput::from_pattern_output(lhs.binxgcd_nz(&rhs));

        // Apply the removed factor 2^k back to the gcd
        let gcd = gcd
            .as_ref()
            .shl(k)
            .to_nz()
            .expect("is non-zero by construction");
        Int::conditional_swap(&mut x, &mut y, swap);
        Uint::conditional_swap(&mut lhs_on_gcd, &mut rhs_on_gcd, swap);

        NonZeroUintXgcdOutput {
            gcd,
            x,
            y,
            lhs_on_gcd,
            rhs_on_gcd,
        }
    }
}

impl<const LIMBS: usize> OddUint<LIMBS> {
    /// Compute the greatest common divisor of `self` and `rhs` using the Binary GCD algorithm.
    ///
    /// This function switches between the "classic" and "optimized" algorithm at a best-effort
    /// threshold. When using [Uint]s with `LIMBS` close to the threshold, it may be useful to
    /// manually test whether the classic or optimized algorithm is faster for your machine.
    #[inline(always)]
    pub const fn bingcd(&self, rhs: &Uint<LIMBS>) -> Self {
        if LIMBS < 8 {
            self.classic_bingcd(rhs)
        } else {
            self.optimized_bingcd(rhs)
        }
    }

    /// Compute the greatest common divisor of `self` and `rhs`.
    ///
    /// Executes in variable time w.r.t. all input parameters.
    ///
    /// This function switches between the "classic" and "optimized" algorithm at a best-effort
    /// threshold. When using [Uint]s with `LIMBS` close to the threshold, it may be useful to
    /// manually test whether the classic or optimized algorithm is faster for your machine.
    #[inline(always)]
    pub const fn bingcd_vartime(&self, rhs: &Uint<LIMBS>) -> Self {
        if LIMBS < 4 {
            self.classic_bingcd_vartime(rhs)
        } else {
            self.optimized_bingcd_vartime(rhs)
        }
    }

    /// Execute the Binary Extended GCD algorithm.
    ///
    /// Given `(self, rhs)`, computes `(g, x, y)` s.t. `self * x + rhs * y = g = gcd(self, rhs)`.
    pub const fn binxgcd(&self, rhs: &Self) -> OddUintXgcdOutput<LIMBS> {
        OddUintXgcdOutput::from_pattern_output(self.classic_binxgcd(rhs).divide())
    }
}

pub type UintXgcdOutput<const LIMBS: usize> = XgcdOutput<LIMBS, Uint<LIMBS>>;
pub type NonZeroUintXgcdOutput<const LIMBS: usize> = XgcdOutput<LIMBS, NonZeroUint<LIMBS>>;
pub type OddUintXgcdOutput<const LIMBS: usize> = XgcdOutput<LIMBS, OddUint<LIMBS>>;

/// Container for the processed output of the Binary XGCD algorithm.
#[derive(Debug, Copy, Clone)]
pub struct XgcdOutput<const LIMBS: usize, GCD: Copy> {
    /// Greatest common divisor
    pub gcd: GCD,
    /// x;
    pub x: Int<LIMBS>,
    /// y;
    pub y: Int<LIMBS>,
    /// lhs / gcd
    pub lhs_on_gcd: Uint<LIMBS>,
    /// rhs / gcd
    pub rhs_on_gcd: Uint<LIMBS>,
}

impl<const LIMBS: usize, GCD: Copy> XgcdOutput<LIMBS, GCD> {
    /// The greatest common divisor stored in this object.
    pub const fn gcd(&self) -> GCD {
        self.gcd
    }

    /// Obtain a copy of the Bézout coefficients.
    pub const fn bezout_coefficients(&self) -> (Int<LIMBS>, Int<LIMBS>) {
        (self.x, self.y)
    }

    /// Obtain a copy of the quotients `lhs/gcd` and `rhs/gcd`.
    pub const fn quotients(&self) -> (Uint<LIMBS>, Uint<LIMBS>) {
        (self.lhs_on_gcd, self.rhs_on_gcd)
    }
}

impl<const LIMBS: usize> OddUintXgcdOutput<LIMBS> {
    pub(crate) const fn from_pattern_output(output: PatternXgcdOutput<LIMBS>) -> Self {
        let gcd = output.gcd();
        let (x, y) = output.bezout_coefficients();
        let (lhs_on_gcd, rhs_on_gcd) = output.quotients();

        OddUintXgcdOutput {
            gcd,
            x,
            y,
            lhs_on_gcd,
            rhs_on_gcd,
        }
    }
}

impl<const LIMBS: usize> Gcd<Uint<LIMBS>> for Uint<LIMBS> {
    type Output = Uint<LIMBS>;

    fn gcd(&self, rhs: &Uint<LIMBS>) -> Self::Output {
        self.bingcd(rhs)
    }

    fn gcd_vartime(&self, rhs: &Uint<LIMBS>) -> Self::Output {
        self.bingcd_vartime(rhs)
    }
}

impl<const LIMBS: usize> Gcd<Int<LIMBS>> for Uint<LIMBS> {
    type Output = Uint<LIMBS>;

    fn gcd(&self, rhs: &Int<LIMBS>) -> Self::Output {
        self.bingcd(&rhs.abs())
    }

    fn gcd_vartime(&self, rhs: &Int<LIMBS>) -> Self::Output {
        self.bingcd_vartime(&rhs.abs())
    }
}

impl<const LIMBS: usize> Gcd<Uint<LIMBS>> for NonZeroUint<LIMBS> {
    type Output = NonZeroUint<LIMBS>;

    fn gcd(&self, rhs: &Uint<LIMBS>) -> Self::Output {
        self.bingcd(rhs)
    }

    fn gcd_vartime(&self, rhs: &Uint<LIMBS>) -> Self::Output {
        self.bingcd_vartime(rhs)
    }
}

impl<const LIMBS: usize> Gcd<Int<LIMBS>> for NonZeroUint<LIMBS> {
    type Output = NonZeroUint<LIMBS>;

    fn gcd(&self, rhs: &Int<LIMBS>) -> Self::Output {
        self.bingcd(&rhs.abs())
    }

    fn gcd_vartime(&self, rhs: &Int<LIMBS>) -> Self::Output {
        self.bingcd_vartime(&rhs.abs())
    }
}

impl<const LIMBS: usize> Gcd<Uint<LIMBS>> for OddUint<LIMBS> {
    type Output = OddUint<LIMBS>;

    fn gcd(&self, rhs: &Uint<LIMBS>) -> Self::Output {
        self.bingcd(rhs)
    }

    fn gcd_vartime(&self, rhs: &Uint<LIMBS>) -> Self::Output {
        self.bingcd_vartime(rhs)
    }
}

impl<const LIMBS: usize> Gcd<Int<LIMBS>> for OddUint<LIMBS> {
    type Output = OddUint<LIMBS>;

    fn gcd(&self, rhs: &Int<LIMBS>) -> Self::Output {
        self.bingcd(&rhs.abs())
    }

    fn gcd_vartime(&self, rhs: &Int<LIMBS>) -> Self::Output {
        self.bingcd_vartime(&rhs.abs())
    }
}

impl<const LIMBS: usize> Xgcd for Uint<LIMBS> {
    type Output = UintXgcdOutput<LIMBS>;

    fn xgcd(&self, rhs: &Uint<LIMBS>) -> Self::Output {
        self.binxgcd(rhs)
    }

    fn xgcd_vartime(&self, rhs: &Uint<LIMBS>) -> Self::Output {
        // TODO(#853): implement vartime
        self.binxgcd(rhs)
    }
}

impl<const LIMBS: usize> Xgcd for NonZeroUint<LIMBS> {
    type Output = NonZeroUintXgcdOutput<LIMBS>;

    fn xgcd(&self, rhs: &NonZeroUint<LIMBS>) -> Self::Output {
        self.binxgcd(rhs)
    }

    fn xgcd_vartime(&self, rhs: &NonZeroUint<LIMBS>) -> Self::Output {
        // TODO(#853): implement vartime
        self.binxgcd(rhs)
    }
}

impl<const LIMBS: usize> Xgcd for OddUint<LIMBS> {
    type Output = OddUintXgcdOutput<LIMBS>;

    fn xgcd(&self, rhs: &OddUint<LIMBS>) -> Self::Output {
        self.binxgcd(rhs)
    }

    fn xgcd_vartime(&self, rhs: &OddUint<LIMBS>) -> Self::Output {
        // TODO(#853): implement vartime
        self.binxgcd(rhs)
    }
}

#[cfg(all(test, not(miri)))]
mod tests {
    mod bingcd {
        use crate::{U64, U128, U256, U512, U1024, U2048, U4096, Uint};

        fn test<const LIMBS: usize>(lhs: Uint<LIMBS>, rhs: Uint<LIMBS>, target: Uint<LIMBS>) {
            assert_eq!(lhs.bingcd(&rhs), target);
            assert_eq!(lhs.bingcd_vartime(&rhs), target)
        }

        fn run_tests<const LIMBS: usize>() {
            test(Uint::<LIMBS>::ZERO, Uint::ZERO, Uint::ZERO);
            test(Uint::<LIMBS>::ZERO, Uint::ONE, Uint::ONE);
            test(Uint::<LIMBS>::ZERO, Uint::MAX, Uint::MAX);
            test(Uint::<LIMBS>::ONE, Uint::ZERO, Uint::ONE);
            test(Uint::<LIMBS>::ONE, Uint::ONE, Uint::ONE);
            test(Uint::<LIMBS>::ONE, Uint::MAX, Uint::ONE);
            test(Uint::<LIMBS>::MAX, Uint::ZERO, Uint::MAX);
            test(Uint::<LIMBS>::MAX, Uint::ONE, Uint::ONE);
            test(Uint::<LIMBS>::MAX, Uint::MAX, Uint::MAX);
        }

        #[test]
        fn bingcd() {
            run_tests::<{ U64::LIMBS }>();
            run_tests::<{ U128::LIMBS }>();
            run_tests::<{ U256::LIMBS }>();
            run_tests::<{ U512::LIMBS }>();
            run_tests::<{ U1024::LIMBS }>();
            run_tests::<{ U2048::LIMBS }>();
            run_tests::<{ U4096::LIMBS }>();
        }
    }

    mod binxgcd {
        use crate::{Concat, Int, U64, U128, U256, U512, U1024, U2048, U4096, U8192, U16384, Uint};
        use core::ops::Div;

        fn test<const LIMBS: usize, const DOUBLE: usize>(lhs: Uint<LIMBS>, rhs: Uint<LIMBS>)
        where
            Uint<LIMBS>: Concat<Output = Uint<DOUBLE>>,
        {
            let output = lhs.binxgcd(&rhs);
            assert_eq!(output.gcd, lhs.bingcd(&rhs));

            if output.gcd > Uint::ZERO {
                assert_eq!(output.lhs_on_gcd, lhs.div(output.gcd.to_nz().unwrap()));
                assert_eq!(output.rhs_on_gcd, rhs.div(output.gcd.to_nz().unwrap()));
            }

            let (x, y) = output.bezout_coefficients();
            assert_eq!(
                x.concatenating_mul_uint(&lhs) + y.concatenating_mul_uint(&rhs),
                *output.gcd.resize().as_int()
            );
        }

        fn run_tests<const LIMBS: usize, const DOUBLE: usize>()
        where
            Uint<LIMBS>: Concat<Output = Uint<DOUBLE>>,
        {
            let min = Int::MIN.abs();
            test(Uint::ZERO, Uint::ZERO);
            test(Uint::ZERO, Uint::ONE);
            test(Uint::ZERO, min);
            test(Uint::ZERO, Uint::MAX);
            test(Uint::ONE, Uint::ZERO);
            test(Uint::ONE, Uint::ONE);
            test(Uint::ONE, min);
            test(Uint::ONE, Uint::MAX);
            test(min, Uint::ZERO);
            test(min, Uint::ONE);
            test(min, Int::MIN.abs());
            test(min, Uint::MAX);
            test(Uint::MAX, Uint::ZERO);
            test(Uint::MAX, Uint::ONE);
            test(Uint::MAX, min);
            test(Uint::MAX, Uint::MAX);
        }

        #[test]
        fn binxgcd() {
            run_tests::<{ U64::LIMBS }, { U128::LIMBS }>();
            run_tests::<{ U128::LIMBS }, { U256::LIMBS }>();
            run_tests::<{ U256::LIMBS }, { U512::LIMBS }>();
            run_tests::<{ U512::LIMBS }, { U1024::LIMBS }>();
            run_tests::<{ U1024::LIMBS }, { U2048::LIMBS }>();
            run_tests::<{ U2048::LIMBS }, { U4096::LIMBS }>();
            run_tests::<{ U4096::LIMBS }, { U8192::LIMBS }>();
            run_tests::<{ U8192::LIMBS }, { U16384::LIMBS }>();
        }

        #[test]
        fn regression_tests() {
            // Sent in by @kayabaNerve (https://github.com/RustCrypto/crypto-bigint/pull/761#issuecomment-2771564732)
            let a = U256::from_be_hex(
                "000000000000000000000000000000000000001B5DFB3BA1D549DFAF611B8D4C",
            );
            let b = U256::from_be_hex(
                "000000000000345EAEDFA8CA03C1F0F5B578A787FE2D23B82A807F178B37FD8E",
            );
            test(a, b);

            // Sent in by @kayabaNerve (https://github.com/RustCrypto/crypto-bigint/pull/761#issuecomment-2771581512)
            let a = U256::from_be_hex(
                "000000000000000000000000000000000000001A0DEEF6F3AC2566149D925044",
            );
            let b = U256::from_be_hex(
                "000000000000072B69C9DD0AA15F135675EA9C5180CF8FF0A59298CFC92E87FA",
            );
            test(a, b);

            // Sent in by @kayabaNerve (https://github.com/RustCrypto/crypto-bigint/pull/761#issuecomment-2782912608)
            let a = U512::from_be_hex(concat![
                "7FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364142",
                "4EB38E6AC0E34DE2F34BFAF22DE683E1F4B92847B6871C780488D797042229E1"
            ]);
            let b = U512::from_be_hex(concat![
                "FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFD755DB9CD5E9140777FA4BD19A06C8283",
                "9D671CD581C69BC5E697F5E45BCD07C52EC373A8BDC598B4493F50A1380E1281"
            ]);
            test(a, b);
        }
    }

    mod traits {
        use crate::{Gcd, I256, U256};

        #[test]
        fn gcd_relatively_prime() {
            // Two semiprimes with no common factors
            let f = U256::from(59u32 * 67);
            let g = U256::from(61u32 * 71);
            let gcd = f.gcd(&g);
            assert_eq!(gcd, U256::ONE);
        }

        #[test]
        fn gcd_nonprime() {
            let f = U256::from(4391633u32);
            let g = U256::from(2022161u32);
            let gcd = f.gcd(&g);
            assert_eq!(gcd, U256::from(1763u32));
        }

        #[test]
        fn gcd_zero() {
            assert_eq!(U256::ZERO.gcd(&U256::ZERO), U256::ZERO);
            assert_eq!(U256::ZERO.gcd(&U256::ONE), U256::ONE);
            assert_eq!(U256::ONE.gcd(&U256::ZERO), U256::ONE);
        }

        #[test]
        fn gcd_one() {
            let f = U256::ONE;
            assert_eq!(U256::ONE, f.gcd(&U256::ONE));
            assert_eq!(U256::ONE, f.gcd(&U256::from(2u8)));
        }

        #[test]
        fn gcd_two() {
            let f = U256::from_u8(2);
            assert_eq!(f, f.gcd(&f));

            let g = U256::from_u8(4);
            assert_eq!(f, f.gcd(&g));
            assert_eq!(f, g.gcd(&f));
        }

        #[test]
        fn gcd_uint_int() {
            // Two numbers with a shared factor of 61
            let f = U256::from(61u32 * 71);
            let g = I256::from(59i32 * 61);

            let sixty_one = U256::from(61u32);
            assert_eq!(sixty_one, <U256 as Gcd<I256>>::gcd(&f, &g));
            assert_eq!(sixty_one, <U256 as Gcd<I256>>::gcd(&f, &g.wrapping_neg()));
        }
    }
}
