//! This module implements (a constant variant of) the Optimized Extended Binary GCD algorithm,
//! which is described by Pornin as Algorithm 2 in "Optimized Binary GCD for Modular Inversion".
//! Ref: <https://eprint.iacr.org/2020/972.pdf>

use crate::modular::bingcd::tools::const_min;
use crate::{NonZero, Odd, Uint};

impl<const LIMBS: usize> Uint<LIMBS> {
    /// Compute the greatest common divisor of `self` and `rhs`.
    pub const fn bingcd(&self, rhs: &Self) -> Self {
        let self_is_zero = self.is_nonzero().not();
        let self_nz = Uint::select(self, &Uint::ONE, self_is_zero)
            .to_nz()
            .expect("self is non zero by construction");
        Uint::select(self_nz.bingcd(rhs).as_ref(), rhs, self_is_zero)
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
}

impl<const LIMBS: usize> Odd<Uint<LIMBS>> {
    /// Compute the greatest common divisor of `self` and `rhs` using the Binary GCD algorithm.
    ///
    /// This function switches between the "classic" and "optimized" algorithm at a best-effort
    /// threshold. When using [Uint]s with `LIMBS` close to the threshold, it may be useful to
    /// manually test whether the classic or optimized algorithm is faster for your machine.
    #[inline(always)]
    pub const fn bingcd(&self, rhs: &Uint<LIMBS>) -> Self {
        // Todo: tweak this threshold
        if LIMBS < 8 {
            self.classic_bingcd(rhs)
        } else {
            self.optimized_bingcd(rhs)
        }
    }
}

#[cfg(feature = "rand_core")]
#[cfg(test)]
mod tests {
    use rand_core::OsRng;

    use crate::{
        Gcd, Int, Random, Uint, U1024, U128, U16384, U2048, U256, U4096, U512, U64, U8192,
    };

    fn bingcd_test<const LIMBS: usize>(lhs: Uint<LIMBS>, rhs: Uint<LIMBS>)
    where
        Uint<LIMBS>: Gcd<Output = Uint<LIMBS>>,
    {
        let gcd = lhs.gcd(&rhs);
        let bingcd = lhs.bingcd(&rhs);
        assert_eq!(gcd, bingcd);
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

        // Randomized test cases
        for _ in 0..100 {
            let x = Uint::<LIMBS>::random(&mut OsRng);
            let y = Uint::<LIMBS>::random(&mut OsRng);
            bingcd_test(x, y);
        }
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
