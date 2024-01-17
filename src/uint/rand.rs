//! Random number generator support

use super::{Uint, Word};
use crate::{Encoding, Limb, NonZero, Random, RandomBits, RandomBitsError, RandomMod, Zero};
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

/// Fill the given limbs slice with random bits.
///
/// NOTE: Assumes that the limbs in the given slice are zeroed!
pub(crate) fn random_bits_core(
    rng: &mut impl CryptoRngCore,
    zeroed_limbs: &mut [Limb],
    bit_length: u32,
) -> Result<(), RandomBitsError> {
    if bit_length == 0 {
        return Ok(());
    }

    let buffer: Word = 0;
    let mut buffer = buffer.to_be_bytes();

    let nonzero_limbs = ((bit_length + Limb::BITS - 1) / Limb::BITS) as usize;
    let partial_limb = bit_length % Limb::BITS;
    let mask = Word::MAX >> ((Word::BITS - partial_limb) % Word::BITS);

    for i in 0..nonzero_limbs - 1 {
        rng.try_fill_bytes(&mut buffer)
            .map_err(RandomBitsError::RandCore)?;
        zeroed_limbs[i] = Limb(Word::from_be_bytes(buffer));
    }

    rng.try_fill_bytes(&mut buffer)
        .map_err(RandomBitsError::RandCore)?;
    zeroed_limbs[nonzero_limbs - 1] = Limb(Word::from_be_bytes(buffer) & mask);

    Ok(())
}

impl<const LIMBS: usize> RandomBits for Uint<LIMBS> {
    fn try_random_bits(
        rng: &mut impl CryptoRngCore,
        bit_length: u32,
    ) -> Result<Self, RandomBitsError> {
        Self::try_random_bits_with_precision(rng, bit_length, Self::BITS)
    }

    fn try_random_bits_with_precision(
        rng: &mut impl CryptoRngCore,
        bit_length: u32,
        bits_precision: u32,
    ) -> Result<Self, RandomBitsError> {
        if bits_precision != Self::BITS {
            return Err(RandomBitsError::BitsPrecisionMismatch {
                bits_precision,
                integer_bits: Self::BITS,
            });
        }
        if bit_length > Self::BITS {
            return Err(RandomBitsError::BitLengthTooLarge {
                bit_length,
                bits_precision,
            });
        }
        let mut limbs = [Limb::ZERO; LIMBS];
        random_bits_core(rng, &mut limbs, bit_length)?;
        Ok(Self::from(limbs))
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
    fn random_mod(rng: &mut impl CryptoRngCore, modulus: &NonZero<Self>) -> Self {
        let mut n = Self::ZERO;
        random_mod_core(rng, &mut n, modulus, modulus.bits_vartime());
        n
    }
}

/// Generic implementation of `random_mod` which can be shared with `BoxedUint`.
// TODO(tarcieri): obtain `n_bits` via a trait like `Integer`
pub(super) fn random_mod_core<T>(
    rng: &mut impl CryptoRngCore,
    n: &mut T,
    modulus: &NonZero<T>,
    n_bits: u32,
) where
    T: AsMut<[Limb]> + ConstantTimeLess + Zero,
{
    let n_bytes = ((n_bits + 7) / 8) as usize;
    let n_limbs = ((n_bits + Limb::BITS - 1) / Limb::BITS) as usize;
    let hi_bytes = n_bytes - (n_limbs - 1) * Limb::BYTES;

    let mut bytes = Limb::ZERO.to_le_bytes();

    loop {
        for i in 0..n_limbs - 1 {
            rng.fill_bytes(bytes.as_mut());
            // Need to deserialize from little-endian to make sure that two 32-bit limbs
            // deserialized sequentially are equal to one 64-bit limb produced from the same
            // byte stream.
            n.as_mut()[i] = Limb::from_le_bytes(bytes);
        }

        // Generate the high limb which may need to only be filled partially.
        bytes = Limb::ZERO.to_le_bytes();
        rng.fill_bytes(&mut bytes[..hi_bytes]);
        n.as_mut()[n_limbs - 1] = Limb::from_le_bytes(bytes);

        if n.ct_lt(modulus).into() {
            break;
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{Limb, NonZero, RandomBits, RandomMod, U256};
    use rand_core::SeedableRng;

    #[test]
    fn random_mod() {
        let mut rng = rand_chacha::ChaCha8Rng::seed_from_u64(1);

        // Ensure `random_mod` runs in a reasonable amount of time
        let modulus = NonZero::new(U256::from(42u8)).unwrap();
        let res = U256::random_mod(&mut rng, &modulus);

        // Check that the value is in range
        assert!(res < U256::from(42u8));

        // Ensure `random_mod` runs in a reasonable amount of time
        // when the modulus is larger than 1 limb
        let modulus = NonZero::new(U256::from(0x10000000000000001u128)).unwrap();
        let res = U256::random_mod(&mut rng, &modulus);

        // Check that the value is in range
        assert!(res < U256::from(0x10000000000000001u128));
    }

    #[test]
    fn random_bits() {
        let mut rng = rand_chacha::ChaCha8Rng::seed_from_u64(1);

        let lower_bound = 16;

        // Full length of the integer
        let bit_length = U256::BITS;
        for _ in 0..10 {
            let res = U256::random_bits(&mut rng, bit_length);
            assert!(res > (U256::ONE << (bit_length - lower_bound)));
        }

        // A multiple of limb size
        let bit_length = U256::BITS - Limb::BITS;
        for _ in 0..10 {
            let res = U256::random_bits(&mut rng, bit_length);
            assert!(res > (U256::ONE << (bit_length - lower_bound)));
            assert!(res < (U256::ONE << bit_length));
        }

        // A multiple of 8
        let bit_length = U256::BITS - Limb::BITS - 8;
        for _ in 0..10 {
            let res = U256::random_bits(&mut rng, bit_length);
            assert!(res > (U256::ONE << (bit_length - lower_bound)));
            assert!(res < (U256::ONE << bit_length));
        }

        // Not a multiple of 8
        let bit_length = U256::BITS - Limb::BITS - 8 - 3;
        for _ in 0..10 {
            let res = U256::random_bits(&mut rng, bit_length);
            assert!(res > (U256::ONE << (bit_length - lower_bound)));
            assert!(res < (U256::ONE << bit_length));
        }

        // One incomplete limb
        let bit_length = 7;
        for _ in 0..10 {
            let res = U256::random_bits(&mut rng, bit_length);
            assert!(res < (U256::ONE << bit_length));
        }

        // Zero bits
        let bit_length = 0;
        for _ in 0..10 {
            let res = U256::random_bits(&mut rng, bit_length);
            assert_eq!(res, U256::ZERO);
        }
    }
}
