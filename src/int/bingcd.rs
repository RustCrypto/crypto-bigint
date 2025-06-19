//! This module implements (a constant variant of) the Optimized Extended Binary GCD algorithm,
//! which is described by Pornin in "Optimized Binary GCD for Modular Inversion".
//! Ref: <https://eprint.iacr.org/2020/972.pdf>

use crate::{Int, NonZero, Odd, Uint};

impl<const LIMBS: usize> Int<LIMBS> {
    /// Compute the gcd of `self` and `rhs` leveraging the Binary GCD algorithm.
    pub const fn bingcd(&self, rhs: &Self) -> Uint<LIMBS> {
        self.abs().bingcd(&rhs.abs())
    }
}

impl<const LIMBS: usize> NonZero<Int<LIMBS>> {
    /// Compute the gcd of `self` and `rhs` leveraging the Binary GCD algorithm.
    pub const fn bingcd(&self, rhs: &Self) -> NonZero<Uint<LIMBS>> {
        self.abs().bingcd(&rhs.as_ref().abs())
    }
}

impl<const LIMBS: usize> Odd<Int<LIMBS>> {
    /// Compute the gcd of `self` and `rhs` leveraging the Binary GCD algorithm.
    pub const fn bingcd(&self, rhs: &Self) -> Odd<Uint<LIMBS>> {
        self.abs().bingcd(&rhs.as_ref().abs())
    }
}

#[cfg(feature = "rand_core")]
#[cfg(test)]
mod tests {
    use rand_chacha::ChaCha8Rng;
    use rand_core::{RngCore, SeedableRng};

    use crate::{Gcd, I64, I128, I256, I512, I1024, I2048, I4096, Int, Random, Uint};

    fn int_bingcd_test<const LIMBS: usize>(lhs: Int<LIMBS>, rhs: Int<LIMBS>)
    where
        Uint<LIMBS>: Gcd<Output = Uint<LIMBS>>,
    {
        let gcd = lhs.abs().gcd(&rhs.abs());
        let bingcd = lhs.bingcd(&rhs);
        assert_eq!(gcd, bingcd);
    }

    fn int_bingcd_tests<const LIMBS: usize>(rng: &mut impl RngCore)
    where
        Uint<LIMBS>: Gcd<Output = Uint<LIMBS>>,
    {
        // Edge cases
        int_bingcd_test(Int::MIN, Int::MIN);
        int_bingcd_test(Int::MIN, Int::MINUS_ONE);
        int_bingcd_test(Int::MIN, Int::ZERO);
        int_bingcd_test(Int::MIN, Int::ONE);
        int_bingcd_test(Int::MIN, Int::MAX);
        int_bingcd_test(Int::MINUS_ONE, Int::MIN);
        int_bingcd_test(Int::MINUS_ONE, Int::MINUS_ONE);
        int_bingcd_test(Int::MINUS_ONE, Int::ZERO);
        int_bingcd_test(Int::MINUS_ONE, Int::ONE);
        int_bingcd_test(Int::MINUS_ONE, Int::MAX);
        int_bingcd_test(Int::ZERO, Int::MIN);
        int_bingcd_test(Int::ZERO, Int::MINUS_ONE);
        int_bingcd_test(Int::ZERO, Int::ZERO);
        int_bingcd_test(Int::ZERO, Int::ONE);
        int_bingcd_test(Int::ZERO, Int::MAX);
        int_bingcd_test(Int::ONE, Int::MIN);
        int_bingcd_test(Int::ONE, Int::MINUS_ONE);
        int_bingcd_test(Int::ONE, Int::ZERO);
        int_bingcd_test(Int::ONE, Int::ONE);
        int_bingcd_test(Int::ONE, Int::MAX);
        int_bingcd_test(Int::MAX, Int::MIN);
        int_bingcd_test(Int::MAX, Int::MINUS_ONE);
        int_bingcd_test(Int::MAX, Int::ZERO);
        int_bingcd_test(Int::MAX, Int::ONE);
        int_bingcd_test(Int::MAX, Int::MAX);

        // Randomized test cases
        for _ in 0..100 {
            let x = Int::<LIMBS>::random(rng);
            let y = Int::<LIMBS>::random(rng);
            int_bingcd_test(x, y);
        }
    }

    #[test]
    fn test_int_bingcd() {
        let mut rng = ChaCha8Rng::from_seed(*b"01234567890123456789012345678901");
        int_bingcd_tests::<{ I64::LIMBS }>(&mut rng);
        int_bingcd_tests::<{ I128::LIMBS }>(&mut rng);
        int_bingcd_tests::<{ I256::LIMBS }>(&mut rng);
        int_bingcd_tests::<{ I512::LIMBS }>(&mut rng);
        int_bingcd_tests::<{ I1024::LIMBS }>(&mut rng);
        int_bingcd_tests::<{ I2048::LIMBS }>(&mut rng);
        int_bingcd_tests::<{ I4096::LIMBS }>(&mut rng);
    }
}
