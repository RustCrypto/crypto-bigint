//! Random number generator support

use super::{Uint, Word};
use crate::{Encoding, Limb, NonZero, Random, RandomBits, RandomBitsError, RandomMod, Zero};
use rand_core::{RngCore, TryRngCore};
use subtle::ConstantTimeLess;

impl<const LIMBS: usize> Random for Uint<LIMBS> {
    fn try_random<R: TryRngCore + ?Sized>(rng: &mut R) -> Result<Self, R::Error> {
        let mut limbs = [Limb::ZERO; LIMBS];

        for limb in &mut limbs {
            *limb = Limb::try_random(rng)?
        }

        Ok(limbs.into())
    }
}

/// Fill the given limbs slice with random bits.
///
/// NOTE: Assumes that the limbs in the given slice are zeroed!
pub(crate) fn random_bits_core<R: TryRngCore + ?Sized>(
    rng: &mut R,
    zeroed_limbs: &mut [Limb],
    bit_length: u32,
) -> Result<(), RandomBitsError<R::Error>> {
    if bit_length == 0 {
        return Ok(());
    }

    let buffer: Word = 0;
    let mut buffer = buffer.to_be_bytes();

    let nonzero_limbs = bit_length.div_ceil(Limb::BITS) as usize;
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
    fn try_random_bits<R: TryRngCore + ?Sized>(
        rng: &mut R,
        bit_length: u32,
    ) -> Result<Self, RandomBitsError<R::Error>> {
        Self::try_random_bits_with_precision(rng, bit_length, Self::BITS)
    }

    fn try_random_bits_with_precision<R: TryRngCore + ?Sized>(
        rng: &mut R,
        bit_length: u32,
        bits_precision: u32,
    ) -> Result<Self, RandomBitsError<R::Error>> {
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
    fn random_mod<R: RngCore + ?Sized>(rng: &mut R, modulus: &NonZero<Self>) -> Self {
        let mut n = Self::ZERO;
        let Ok(()) = random_mod_core(rng, &mut n, modulus, modulus.bits_vartime());
        n
    }

    fn try_random_mod<R: TryRngCore + ?Sized>(
        rng: &mut R,
        modulus: &NonZero<Self>,
    ) -> Result<Self, R::Error> {
        let mut n = Self::ZERO;
        random_mod_core(rng, &mut n, modulus, modulus.bits_vartime())?;
        Ok(n)
    }
}

/// Generic implementation of `random_mod` which can be shared with `BoxedUint`.
// TODO(tarcieri): obtain `n_bits` via a trait like `Integer`
pub(super) fn random_mod_core<T, R: TryRngCore + ?Sized>(
    rng: &mut R,
    n: &mut T,
    modulus: &NonZero<T>,
    n_bits: u32,
) -> Result<(), R::Error>
where
    T: AsMut<[Limb]> + AsRef<[Limb]> + ConstantTimeLess + Zero,
{
    #[cfg(target_pointer_width = "64")]
    let mut next_word = || rng.try_next_u64();
    #[cfg(target_pointer_width = "32")]
    let mut next_word = || rng.try_next_u32();

    let n_limbs = n_bits.div_ceil(Limb::BITS) as usize;

    let hi_word_modulus = modulus.as_ref().as_ref()[n_limbs - 1].0;
    let mask = !0 >> hi_word_modulus.leading_zeros();
    let mut hi_word = next_word()? & mask;

    loop {
        while hi_word > hi_word_modulus {
            hi_word = next_word()? & mask;
        }
        // Set high limb
        n.as_mut()[n_limbs - 1] = Limb::from_le_bytes(hi_word.to_le_bytes());
        // Set low limbs
        for i in 0..n_limbs - 1 {
            // Need to deserialize from little-endian to make sure that two 32-bit limbs
            // deserialized sequentially are equal to one 64-bit limb produced from the same
            // byte stream.
            n.as_mut()[i] = Limb::from_le_bytes(next_word()?.to_le_bytes());
        }
        // If the high limb is equal to the modulus' high limb, it's still possible
        // that the full uint is too big so we check and repeat if it is.
        if n.ct_lt(modulus).into() {
            break;
        }
        hi_word = next_word()? & mask;
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use crate::{Limb, NonZero, RandomBits, RandomMod, U256};
    use rand_chacha::ChaCha8Rng;
    use rand_core::SeedableRng;

    #[test]
    fn random_mod() {
        let mut rng = ChaCha8Rng::seed_from_u64(1);

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
        let mut rng = ChaCha8Rng::seed_from_u64(1);

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
