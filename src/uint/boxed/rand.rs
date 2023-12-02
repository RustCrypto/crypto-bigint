//! Random number generator support.

use super::BoxedUint;
use crate::{uint::rand::random_mod_core, Limb, NonZero, Random, RandomMod};
use rand_core::CryptoRngCore;

impl BoxedUint {
    /// Generate a cryptographically secure random [`BoxedUint`].
    /// in range `[0, 2^bits_precision)`.
    pub fn random(rng: &mut impl CryptoRngCore, bits_precision: u32) -> Self {
        let mut ret = BoxedUint::zero_with_precision(bits_precision);

        for limb in &mut *ret.limbs {
            *limb = Limb::random(rng)
        }

        // Since `bits_precision` will be rounded up on creation of `ret`,
        // we need to clear the high bits if the rounding occurred.
        ret.limbs[ret.limbs.len() - 1] =
            ret.limbs[ret.limbs.len() - 1] & (Limb::MAX >> (ret.bits_precision() - bits_precision));

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
    use crate::{BoxedUint, NonZero, RandomMod};
    use rand_core::SeedableRng;

    #[test]
    fn random() {
        let mut rng = rand_chacha::ChaCha8Rng::seed_from_u64(1);

        let r = BoxedUint::random(&mut rng, 256);
        assert!(r.bits_precision() == 256);

        let r = BoxedUint::random(&mut rng, 256 - 32 + 1);
        assert!(r.bits_precision() == 256);
        assert!(r < BoxedUint::one_with_precision(256) << (256 - 32 + 1));
    }

    #[test]
    fn random_mod() {
        let mut rng = rand_chacha::ChaCha8Rng::seed_from_u64(1);

        // Ensure `random_mod` runs in a reasonable amount of time
        let modulus = NonZero::new(BoxedUint::from(42u8)).unwrap();
        let res = BoxedUint::random_mod(&mut rng, &modulus);

        // Check that the value is in range
        assert!(res < BoxedUint::from(42u8));

        // Ensure `random_mod` runs in a reasonable amount of time
        // when the modulus is larger than 1 limb
        let modulus = NonZero::new(BoxedUint::from(0x10000000000000001u128)).unwrap();
        let res = BoxedUint::random_mod(&mut rng, &modulus);

        // Check that the value is in range
        assert!(res < BoxedUint::from(0x10000000000000001u128));
    }
}
