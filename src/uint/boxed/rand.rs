//! Random number generator support.

use super::BoxedUint;
use crate::{uint::rand::random_mod_core, Limb, NonZero, Random, RandomMod};
use rand_core::CryptoRngCore;

impl BoxedUint {
    /// Generate a cryptographically secure random [`BoxedUint`].
    pub fn random(mut rng: &mut impl CryptoRngCore, bits_precision: u32) -> Self {
        let mut ret = BoxedUint::zero_with_precision(bits_precision);

        for limb in &mut *ret.limbs {
            *limb = Limb::random(&mut rng)
        }

        ret
    }
}

impl RandomMod for BoxedUint {
    /// Generate a cryptographically secure random [`BoxedUint`] which is less than a given
    /// `modulus`.
    ///
    /// This function uses rejection sampling, a method which produces an unbiased distribution of
    /// in-range values provided the underlying CSRNG is unbiased, but runs in variable-time.
    ///
    /// The variable-time nature of the algorithm should not pose a security issue so long as the
    /// underlying random number generator is truly a CSRNG, where previous outputs are unrelated to
    /// subsequent outputs and do not reveal information about the RNG's internal state.
    fn random_mod(rng: &mut impl CryptoRngCore, modulus: &NonZero<Self>) -> Self {
        let mut n = BoxedUint::zero_with_precision(modulus.bits_precision());
        random_mod_core(rng, &mut n, modulus, modulus.bits());
        n
    }
}

#[cfg(test)]
mod tests {
    use crate::{NonZero, RandomMod, U256};
    use rand_core::SeedableRng;

    #[test]
    fn random_mod() {
        let mut rng = rand_chacha::ChaCha8Rng::seed_from_u64(1);

        // Ensure `random_mod` runs in a reasonable amount of time
        let modulus = NonZero::new(U256::from(42u8)).unwrap();
        let res = U256::random_mod(&mut rng, &modulus);

        // Check that the value is in range
        assert!(res >= U256::ZERO);
        assert!(res < U256::from(42u8));

        // Ensure `random_mod` runs in a reasonable amount of time
        // when the modulus is larger than 1 limb
        let modulus = NonZero::new(U256::from(0x10000000000000001u128)).unwrap();
        let res = U256::random_mod(&mut rng, &modulus);

        // Check that the value is in range
        assert!(res >= U256::ZERO);
        assert!(res < U256::from(0x10000000000000001u128));
    }
}
