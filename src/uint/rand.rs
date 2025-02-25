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
        zeroed_limbs[i] = Limb(Word::from_le_bytes(buffer));
    }

    // This algorithm should sample the same number of random bytes, regardless of the pointer width
    // of the target platform. To this end, special attention has to be paid to the case where
    // bit_length - 1 < 32 mod 64. Bit strings of that size can be represented using `2X+1` 32-bit
    // words or `X+1` 64-bit words. Note that 64*(X+1) - 32*(2X+1) = 32. Hence, if we sample full
    // words only, a 64-bit platform will sample 32 bits more than a 32-bit platform. We prevent
    // this by forcing both platforms to only sample 4 bytes for the last word in this case.
    let slice = if partial_limb > 0 && partial_limb <= 32 {
        // Note: we do not have to zeroize the second half of the buffer, as the mask will take
        // care of this in the end.
        &mut buffer[0..4]
    } else {
        buffer.as_mut_slice()
    };

    rng.try_fill_bytes(slice)
        .map_err(RandomBitsError::RandCore)?;
    zeroed_limbs[nonzero_limbs - 1] = Limb(Word::from_le_bytes(buffer) & mask);

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
    use crate::uint::rand::random_bits_core;
    use crate::{Limb, NonZero, RandomBits, RandomMod, Uint, U1024, U256};
    use rand_chacha::ChaCha8Rng;
    use rand_chacha::{ChaCha20Core, ChaCha20Rng};
    use rand_core::{RngCore, SeedableRng};

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

    /// Make sure the random_bits output is consistent across platforms
    #[test]
    fn random_bits_platform_independence() {
        let zero_seed = [0u8; 32];
        let mut rng = ChaCha20Rng::from(ChaCha20Core::from_seed(zero_seed));

        let mut val = U1024::ZERO;
        let bytes = val.as_limbs_mut().as_mut_slice();
        random_bits_core(&mut rng, bytes, 989).expect("safe");

        assert_eq!(
            val,
            Uint::from_be_hex(concat![
                "000000001F0AE1AC45FB0A51281FED31D539D874B03371D5434EE69C7621B729",
                "ED7AEE323E53C6126965E348A0290FCB0D082D737C97BA987A385155BEE7079F",
                "8665EEB269B687C31CA11815F4B8436A374AD8B83FE024778D4857517C5941DA",
                "C70D778BCCEF36A81AED8DA0B819D2BD28BD8653E56A5D40903DF1A0ADE0B876"
            ])
        );

        // Test that the RNG is in the same state
        let mut state = [0u8; 16];
        rng.fill_bytes(&mut state);

        assert_eq!(
            state,
            [75, 121, 77, 111, 45, 9, 160, 230, 99, 38, 108, 225, 174, 126, 209, 8]
        );
    }
}
