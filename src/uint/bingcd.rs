//! This module implements (a constant variant of) the Optimized Extended Binary GCD algorithm,
//! which is described by Pornin as Algorithm 2 in "Optimized Binary GCD for Modular Inversion".
//! Ref: <https://eprint.iacr.org/2020/972.pdf>

use crate::modular::bingcd::tools::const_min;
use crate::modular::bingcd::{NonZeroUintBinxgcdOutput, OddUintBinxgcdOutput, UintBinxgcdOutput};
use crate::{ConstChoice, Int, NonZero, Odd, Uint};

impl<const LIMBS: usize> Uint<LIMBS> {
    /// Compute the greatest common divisor of `self` and `rhs`.
    pub const fn bingcd(&self, rhs: &Self) -> Self {
        let self_is_zero = self.is_nonzero().not();
        let self_nz = Uint::select(self, &Uint::ONE, self_is_zero)
            .to_nz()
            .expect("self is non zero by construction");
        Uint::select(self_nz.bingcd(rhs).as_ref(), rhs, self_is_zero)
    }

    /// Executes the Binary Extended GCD algorithm.
    ///
    /// Given `(self, rhs)`, computes `(g, x, y)`, s.t. `self * x + rhs * y = g = gcd(self, rhs)`.
    pub const fn binxgcd(&self, rhs: &Self) -> UintBinxgcdOutput<LIMBS> {
        // Make sure `self` and `rhs` are nonzero.
        let self_is_zero = self.is_nonzero().not();
        let self_nz = Uint::select(self, &Uint::ONE, self_is_zero)
            .to_nz()
            .expect("self is non zero by construction");
        let rhs_is_zero = rhs.is_nonzero().not();
        let rhs_nz = Uint::select(rhs, &Uint::ONE, rhs_is_zero)
            .to_nz()
            .expect("rhs is non zero by construction");

        let NonZeroUintBinxgcdOutput {
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

        UintBinxgcdOutput {
            gcd,
            x,
            y,
            lhs_on_gcd,
            rhs_on_gcd,
        }
    }
}

impl<const LIMBS: usize> NonZero<Uint<LIMBS>> {
    /// Compute the greatest common divisor of `self` and `rhs`.
    pub const fn bingcd(&self, rhs: &Uint<LIMBS>) -> Self {
        let val = self.as_ref();
        // Leverage two GCD identity rules to make self odd.
        // 1) gcd(2a, 2b) = 2 * gcd(a, b)
        // 2) gcd(a, 2b) = gcd(a, b) if a is odd.
        let i = val.trailing_zeros();
        let j = rhs.trailing_zeros();
        let k = const_min(i, j);

        val.shr(i)
            .to_odd()
            .expect("val.shr(i) is odd by construction")
            .bingcd(rhs)
            .as_ref()
            .shl(k)
            .to_nz()
            .expect("gcd of non-zero element with another element is non-zero")
    }

    /// Execute the Binary Extended GCD algorithm.
    ///
    /// Given `(self, rhs)`, computes `(g, x, y)` s.t. `self * x + rhs * y = g = gcd(self, rhs)`.
    pub const fn binxgcd(&self, rhs: &Self) -> NonZeroUintBinxgcdOutput<LIMBS> {
        let (mut lhs, mut rhs) = (*self.as_ref(), *rhs.as_ref());

        // Leverage the property that gcd(2^k * a, 2^k *b) = 2^k * gcd(a, b)
        let i = lhs.trailing_zeros();
        let j = rhs.trailing_zeros();
        let k = const_min(i, j);
        lhs = lhs.shr(k);
        rhs = rhs.shr(k);

        // Note: at this point, either lhs or rhs is odd (or both).
        // Swap to make sure lhs is odd.
        let swap = ConstChoice::from_u32_lt(j, i);
        Uint::conditional_swap(&mut lhs, &mut rhs, swap);
        let lhs = lhs.to_odd().expect("odd by construction");

        let rhs = rhs.to_nz().expect("non-zero by construction");
        let OddUintBinxgcdOutput {
            gcd,
            mut x,
            mut y,
            mut lhs_on_gcd,
            mut rhs_on_gcd,
        } = lhs.binxgcd_nz(&rhs);

        let gcd = gcd
            .as_ref()
            .shl(k)
            .to_nz()
            .expect("is non-zero by construction");
        Int::conditional_swap(&mut x, &mut y, swap);
        Uint::conditional_swap(&mut lhs_on_gcd, &mut rhs_on_gcd, swap);

        NonZeroUintBinxgcdOutput {
            gcd,
            x,
            y,
            lhs_on_gcd,
            rhs_on_gcd,
        }
    }
}

impl<const LIMBS: usize> Odd<Uint<LIMBS>> {
    /// Compute the greatest common divisor of `self` and `rhs` using the Binary GCD algorithm.
    ///
    /// This function switches between the "classic" and "optimized" algorithm at a best-effort
    /// threshold. When using [Uint]s with `LIMBS` close to the threshold, it may be useful to
    /// manually test whether the classic or optimized algorithm is faster for your machine.
    #[inline(always)]
    pub const fn bingcd(&self, rhs: &Uint<LIMBS>) -> Self {
        if LIMBS < 6 {
            self.classic_bingcd(rhs)
        } else {
            self.optimized_bingcd(rhs)
        }
    }

    /// Execute the Binary Extended GCD algorithm.
    ///
    /// Given `(self, rhs)`, computes `(g, x, y)` s.t. `self * x + rhs * y = g = gcd(self, rhs)`.
    pub const fn binxgcd(&self, rhs: &Self) -> OddUintBinxgcdOutput<LIMBS> {
        self.binxgcd_(rhs).process()
    }
}

#[cfg(test)]
mod tests {
    mod bincgd_test {
        #[cfg(feature = "rand_core")]
        use crate::Random;
        #[cfg(feature = "rand_core")]
        use rand_chacha::ChaChaRng;
        #[cfg(feature = "rand_core")]
        use rand_core::SeedableRng;

        use crate::{Gcd, Int, U64, U128, U256, U512, U1024, U2048, U4096, U8192, U16384, Uint};

        fn bingcd_test<const LIMBS: usize>(lhs: Uint<LIMBS>, rhs: Uint<LIMBS>)
        where
            Uint<LIMBS>: Gcd<Output = Uint<LIMBS>>,
        {
            let gcd = lhs.gcd(&rhs);
            let bingcd = lhs.bingcd(&rhs);
            assert_eq!(gcd, bingcd);
        }

        #[cfg(feature = "rand_core")]
        fn bingcd_randomized_tests<const LIMBS: usize>(iterations: u32)
        where
            Uint<LIMBS>: Gcd<Output = Uint<LIMBS>>,
        {
            let mut rng = ChaChaRng::from_seed([0; 32]);
            for _ in 0..iterations {
                let x = Uint::<LIMBS>::random(&mut rng);
                let y = Uint::<LIMBS>::random(&mut rng);
                bingcd_test(x, y);
            }
        }

        fn bingcd_tests<const LIMBS: usize>()
        where
            Uint<LIMBS>: Gcd<Output = Uint<LIMBS>>,
        {
            // Edge cases
            let min = Int::MIN.abs();
            bingcd_test(Uint::ZERO, Uint::ZERO);
            bingcd_test(Uint::ZERO, Uint::ONE);
            bingcd_test(Uint::ZERO, min);
            bingcd_test(Uint::ZERO, Uint::MAX);
            bingcd_test(Uint::ONE, Uint::ZERO);
            bingcd_test(Uint::ONE, Uint::ONE);
            bingcd_test(Uint::ONE, min);
            bingcd_test(Uint::ONE, Uint::MAX);
            bingcd_test(min, Uint::ZERO);
            bingcd_test(min, Uint::ONE);
            bingcd_test(min, Int::MIN.abs());
            bingcd_test(min, Uint::MAX);
            bingcd_test(Uint::MAX, Uint::ZERO);
            bingcd_test(Uint::MAX, Uint::ONE);
            bingcd_test(Uint::ONE, min);
            bingcd_test(Uint::MAX, Uint::MAX);

            #[cfg(feature = "rand_core")]
            bingcd_randomized_tests(100);
        }

        #[test]
        fn test_bingcd() {
            bingcd_tests::<{ U64::LIMBS }>();
            bingcd_tests::<{ U128::LIMBS }>();
            bingcd_tests::<{ U256::LIMBS }>();
            bingcd_tests::<{ U512::LIMBS }>();
            bingcd_tests::<{ U1024::LIMBS }>();
            bingcd_tests::<{ U2048::LIMBS }>();
            bingcd_tests::<{ U4096::LIMBS }>();
            bingcd_tests::<{ U8192::LIMBS }>();
            bingcd_tests::<{ U16384::LIMBS }>();
        }
    }

    mod binxgcd_test {
        use core::ops::Div;

        #[cfg(feature = "rand_core")]
        use crate::Random;
        #[cfg(feature = "rand_core")]
        use rand_chacha::ChaChaRng;
        #[cfg(feature = "rand_core")]
        use rand_core::SeedableRng;

        use crate::{
            Concat, Gcd, Int, U64, U128, U256, U512, U1024, U2048, U4096, U8192, U16384, Uint,
        };

        fn binxgcd_test<const LIMBS: usize, const DOUBLE: usize>(lhs: Uint<LIMBS>, rhs: Uint<LIMBS>)
        where
            Uint<LIMBS>: Gcd<Output = Uint<LIMBS>> + Concat<Output = Uint<DOUBLE>>,
        {
            let output = lhs.binxgcd(&rhs);

            assert_eq!(output.gcd, lhs.gcd(&rhs));

            if output.gcd > Uint::ZERO {
                assert_eq!(output.lhs_on_gcd, lhs.div(output.gcd.to_nz().unwrap()));
                assert_eq!(output.rhs_on_gcd, rhs.div(output.gcd.to_nz().unwrap()));
            }

            let (x, y) = output.bezout_coefficients();
            assert_eq!(
                x.widening_mul_uint(&lhs) + y.widening_mul_uint(&rhs),
                output.gcd.resize().as_int()
            );
        }

        #[cfg(feature = "rand_core")]
        fn binxgcd_randomized_tests<const LIMBS: usize, const DOUBLE: usize>(iterations: u32)
        where
            Uint<LIMBS>: Gcd<Output = Uint<LIMBS>> + Concat<Output = Uint<DOUBLE>>,
        {
            let mut rng = ChaChaRng::from_seed([0; 32]);
            for _ in 0..iterations {
                let x = Uint::<LIMBS>::random(&mut rng);
                let y = Uint::<LIMBS>::random(&mut rng);
                binxgcd_test(x, y);
            }
        }

        fn binxgcd_tests<const LIMBS: usize, const DOUBLE: usize>()
        where
            Uint<LIMBS>: Gcd<Output = Uint<LIMBS>> + Concat<Output = Uint<DOUBLE>>,
        {
            // Edge cases
            let min = Int::MIN.abs();
            binxgcd_test(Uint::ZERO, Uint::ZERO);
            binxgcd_test(Uint::ZERO, Uint::ONE);
            binxgcd_test(Uint::ZERO, min);
            binxgcd_test(Uint::ZERO, Uint::MAX);
            binxgcd_test(Uint::ONE, Uint::ZERO);
            binxgcd_test(Uint::ONE, Uint::ONE);
            binxgcd_test(Uint::ONE, min);
            binxgcd_test(Uint::ONE, Uint::MAX);
            binxgcd_test(min, Uint::ZERO);
            binxgcd_test(min, Uint::ONE);
            binxgcd_test(min, Int::MIN.abs());
            binxgcd_test(min, Uint::MAX);
            binxgcd_test(Uint::MAX, Uint::ZERO);
            binxgcd_test(Uint::MAX, Uint::ONE);
            binxgcd_test(Uint::ONE, min);
            binxgcd_test(Uint::MAX, Uint::MAX);

            #[cfg(feature = "rand_core")]
            binxgcd_randomized_tests(100);
        }

        #[test]
        fn test_binxgcd() {
            binxgcd_tests::<{ U64::LIMBS }, { U128::LIMBS }>();
            binxgcd_tests::<{ U128::LIMBS }, { U256::LIMBS }>();
            binxgcd_tests::<{ U256::LIMBS }, { U512::LIMBS }>();
            binxgcd_tests::<{ U512::LIMBS }, { U1024::LIMBS }>();
            binxgcd_tests::<{ U1024::LIMBS }, { U2048::LIMBS }>();
            binxgcd_tests::<{ U2048::LIMBS }, { U4096::LIMBS }>();
            binxgcd_tests::<{ U4096::LIMBS }, { U8192::LIMBS }>();
            binxgcd_tests::<{ U8192::LIMBS }, { U16384::LIMBS }>();
        }
    }
}
