//! Random number generator support

use super::Uint;
use crate::{Limb, NonZero, Random, RandomMod, RandomPrime};
use rand_core::CryptoRngCore;
use subtle::ConstantTimeLess;

impl<const LIMBS: usize> Random for Uint<LIMBS> {
    /// Generate a cryptographically secure random [`Uint`].
    fn random(mut rng: &mut impl CryptoRngCore) -> Self {
        let mut limbs = [Limb::ZERO; LIMBS];

        for limb in &mut limbs {
            *limb = Limb::random(&mut rng)
        }

        limbs.into()
    }
}

impl<const LIMBS: usize> RandomMod for Uint<LIMBS> {
    /// Generate a cryptographically secure random [`Uint`] which is less than
    /// a given `modulus`.
    ///
    /// This function uses rejection sampling, a method which produces an
    /// unbiased distribution of in-range values provided the underlying
    /// CSRNG is unbiased, but runs in variable-time.
    ///
    /// The variable-time nature of the algorithm should not pose a security
    /// issue so long as the underlying random number generator is truly a
    /// CSRNG, where previous outputs are unrelated to subsequent
    /// outputs and do not reveal information about the RNG's internal state.
    fn random_mod(mut rng: &mut impl CryptoRngCore, modulus: &NonZero<Self>) -> Self {
        let mut n = Self::ZERO;

        let n_bits = modulus.as_ref().bits_vartime();
        let n_limbs = (n_bits + Limb::BITS - 1) / Limb::BITS;
        let mask = Limb::MAX >> (Limb::BITS * n_limbs - n_bits);

        loop {
            for i in 0..n_limbs {
                n.limbs[i] = Limb::random(&mut rng);
            }
            n.limbs[n_limbs - 1] = n.limbs[n_limbs - 1] & mask;

            if n.ct_lt(modulus).into() {
                return n;
            }
        }
    }
}

impl<const LIMBS: usize> RandomPrime for Uint<LIMBS> {
    /// Generate a cryptographically secure random [`Uint`].
    ///
    /// This function uses Miller-Rabin primality test with k=50 rounds
    /// so the probability of returning a composite number is 4^(-50).
    /// Note this method doesn't check whether the generated number
    /// is a safe prime (i.e. that (p-1)/2 is also prime).
    ///
    /// The variable-time nature of the algorithm should not pose a security
    /// issue so long as the underlying random number generator is truly a
    /// CSRNG, where previous outputs are unrelated to subsequent
    /// outputs and do not reveal information about the RNG's internal state.
    fn random_prime(rng: &mut impl CryptoRngCore) -> Self {
        loop {
            let candidate = Self::random(rng);
            if candidate.is_prime_miller_rabin_vartime(rng, 50) {
                return candidate;
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{NonZero, RandomMod, RandomPrime, U1024, U256};
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

    #[test]
    fn random_prime() {
        let mut rng = rand_chacha::ChaCha8Rng::seed_from_u64(1);

        let res = U1024::random_prime(&mut rng);
        // openssl prime -hex DC1DAB4D998BEA51033B81FA7CB97D92B19C11313F04C663D9E8075C2AD0F847AB1E4B28D0E0A6C58A87658B4512FB693C10DEC5341895D855A26C98A259C74B8AC1D7F1F57B56B9D6FB99D23BFAC23B21EE44872E9E9C9BBD22C4301D9BF1B5C80C0A33C139F0BE4477A4EED81ABCE305AD35FE5D598BE2C6FE0EC445F6EDA5
        // outputs "is prime"
        assert_eq!(
            U1024::from_be_hex("DC1DAB4D998BEA51033B81FA7CB97D92B19C11313F04C663D9E8075C2AD0F847AB1E4B28D0E0A6C58A87658B4512FB693C10DEC5341895D855A26C98A259C74B8AC1D7F1F57B56B9D6FB99D23BFAC23B21EE44872E9E9C9BBD22C4301D9BF1B5C80C0A33C139F0BE4477A4EED81ABCE305AD35FE5D598BE2C6FE0EC445F6EDA5"), 
            res
        );
    }
}
