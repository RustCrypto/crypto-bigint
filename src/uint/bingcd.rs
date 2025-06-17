//! This module implements Binary GCD for [`Uint`]

use crate::const_choice::u32_const_min;
use crate::{NonZero, NonZeroUint, Odd, OddUint, Uint};

impl<const LIMBS: usize> Uint<LIMBS> {
    /// Compute the greatest common divisor of `self` and `rhs`.
    pub const fn bingcd(&self, rhs: &Self) -> Self {
        let self_is_zero = self.is_nonzero().not();
        // Note: is non-zero by construction
        let self_nz = NonZero(Uint::select(self, &Uint::ONE, self_is_zero));
        Uint::select(self_nz.bingcd(rhs).as_ref(), rhs, self_is_zero)
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

        let i = lhs.is_nonzero().select_u32(0, lhs.trailing_zeros());
        let j = rhs.is_nonzero().select_u32(0, rhs.trailing_zeros());
        let k = u32_const_min(i, j);

        let odd_lhs = Odd(lhs.shr(i));
        let gcd_div_2k = odd_lhs.bingcd(rhs);
        NonZero(gcd_div_2k.as_ref().shl(k))
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
    use rand_chacha::ChaCha8Rng;
    use rand_core::{RngCore, SeedableRng};

    use crate::{Gcd, Random, U256, U512, U1024, U2048, U4096, U8192, U16384, Uint};

    fn bingcd_test<const LIMBS: usize>(lhs: Uint<LIMBS>, rhs: Uint<LIMBS>)
    where
        Uint<LIMBS>: Gcd<Output = Uint<LIMBS>>,
    {
        let gcd = lhs.gcd(&rhs);
        let bingcd = lhs.bingcd(&rhs);
        assert_eq!(gcd, bingcd);
    }

    fn bingcd_tests<const LIMBS: usize>(rng: &mut impl RngCore)
    where
        Uint<LIMBS>: Gcd<Output = Uint<LIMBS>>,
    {
        // Edge cases
        bingcd_test(Uint::ZERO, Uint::ZERO);
        bingcd_test(Uint::ZERO, Uint::ONE);
        bingcd_test(Uint::ZERO, Uint::MAX);
        bingcd_test(Uint::ONE, Uint::ZERO);
        bingcd_test(Uint::ONE, Uint::ONE);
        bingcd_test(Uint::ONE, Uint::MAX);
        bingcd_test(Uint::MAX, Uint::ZERO);
        bingcd_test(Uint::MAX, Uint::ONE);
        bingcd_test(Uint::MAX, Uint::MAX);

        // Randomized test cases
        for _ in 0..100 {
            let x = Uint::<LIMBS>::random(rng);
            let y = Uint::<LIMBS>::random(rng);
            bingcd_test(x, y);
        }
    }

    #[test]
    fn test_bingcd() {
        let mut rng = ChaCha8Rng::from_seed(*b"01234567890123456789012345678901");
        bingcd_tests::<{ U256::LIMBS }>(&mut rng);
        bingcd_tests::<{ U512::LIMBS }>(&mut rng);
        bingcd_tests::<{ U1024::LIMBS }>(&mut rng);
        bingcd_tests::<{ U2048::LIMBS }>(&mut rng);
        bingcd_tests::<{ U4096::LIMBS }>(&mut rng);
        bingcd_tests::<{ U8192::LIMBS }>(&mut rng);
        bingcd_tests::<{ U16384::LIMBS }>(&mut rng);
    }
}
