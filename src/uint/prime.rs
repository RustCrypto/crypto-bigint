use super::Uint;
#[cfg(feature = "rand_core")]
use crate::modular::runtime_mod::{DynResidue, DynResidueParams};
#[cfg(feature = "rand_core")]
use crate::NonZero;
#[cfg(feature = "rand_core")]
use crate::RandomMod;
#[cfg(feature = "rand_core")]
use core::cmp::Ordering;
#[cfg(feature = "rand_core")]
use rand_core::CryptoRngCore;

impl<const LIMBS: usize> Uint<LIMBS> {
    /// Miller-Rabin probabilistic primality test. Variable-time.
    ///
    /// Returns `false` (number is composite) with certainty.
    /// `true` means that the number is prime with high probability
    /// Panics if the number of rounds is 0.
    /// Probability of false positive decreases as 4^(-k) with the number of rounds `k`
    /// See also <https://en.wikipedia.org/wiki/Miller-Rabin_primality_test>
    #[cfg(feature = "rand_core")]
    pub fn is_prime_miller_rabin_vartime(&self, rng: &mut impl CryptoRngCore, k: usize) -> bool {
        if k == 0 {
            panic!("number of rounds should be greater than 0");
        }

        if self.cmp_vartime(&Uint::ONE) != Ordering::Greater {
            return false;
        }
        // Safe to wrap as we check that `self` is greater than 1 above
        let minus_one = self.wrapping_sub(&Uint::ONE);
        // special case `self` is 2
        if minus_one.cmp_vartime(&Uint::ONE) == Ordering::Equal {
            return true;
        }

        // all even are composite
        if self.ct_is_odd().to_u8() == 0 {
            return false;
        }

        // Decompose `self - 1 = d * 2^t` where `d` is odd
        let t = minus_one.trailing_zeros();
        let d = minus_one.shr(t);

        #[inline]
        fn get_random_base<const LIMBS: usize>(
            rng: &mut impl CryptoRngCore,
            upper: &NonZero<Uint<LIMBS>>,
        ) -> Uint<LIMBS> {
            loop {
                let base = Uint::random_mod(rng, upper);
                if base.cmp_vartime(&Uint::ONE) == Ordering::Greater {
                    return base;
                }
            }
        }

        #[inline]
        fn mod_pow<const LIMBS: usize>(
            base: &Uint<LIMBS>,
            exponent: &Uint<LIMBS>,
            modulus: &Uint<LIMBS>,
        ) -> Uint<LIMBS> {
            let modulus = DynResidueParams::new(modulus);
            let base = DynResidue::new(base, modulus);
            base.pow(exponent).retrieve()
        }

        // Safe as `self` is greater than 2
        let minus_two = NonZero::new(minus_one.wrapping_sub(&Uint::ONE)).unwrap();
        // Special case 3 as random base is drawn from 2 to `self - 2` interval
        if minus_two.cmp_vartime(&Uint::ONE) == Ordering::Equal {
            return true;
        }
        for _ in 0..k {
            let base = get_random_base(rng, &minus_two);
            let mut x = mod_pow(&base, &d, self);
            let mut y = x;
            for _ in 0..t {
                y = mod_pow(&x, &Uint::from(2u8), self);
                if y.cmp_vartime(&Uint::ONE) == Ordering::Equal
                    && x.cmp_vartime(&Uint::ONE) != Ordering::Equal
                    && x.cmp_vartime(&minus_one) != Ordering::Equal
                {
                    return false;
                }
                x = y;
            }
            if y.cmp_vartime(&Uint::ONE) != Ordering::Equal {
                return false;
            }
        }
        true // probably
    }
}

#[cfg(test)]
mod tests {
    #[cfg(feature = "rand_core")]
    use crate::U64;
    #[cfg(feature = "rand_core")]
    use rand_core::SeedableRng;

    #[cfg(feature = "rand_core")]
    #[test]
    fn test_miller_rabin() {
        let mut rng = rand_chacha::ChaCha8Rng::seed_from_u64(1);
        assert!(!U64::from(0u8).is_prime_miller_rabin_vartime(&mut rng, 2));
        assert!(!U64::from(1u8).is_prime_miller_rabin_vartime(&mut rng, 2));
        assert!(U64::from(2u8).is_prime_miller_rabin_vartime(&mut rng, 2));
        assert!(U64::from(3u8).is_prime_miller_rabin_vartime(&mut rng, 2));
        assert!(!U64::from(4u8).is_prime_miller_rabin_vartime(&mut rng, 2));
        assert!(U64::from(5u8).is_prime_miller_rabin_vartime(&mut rng, 2));
        assert!(!U64::from(6u8).is_prime_miller_rabin_vartime(&mut rng, 2));
        assert!(U64::from(7u8).is_prime_miller_rabin_vartime(&mut rng, 2));
        assert!(U64::from(89u8).is_prime_miller_rabin_vartime(&mut rng, 2));
        // Carmichael number is composite (see https://en.wikipedia.org/wiki/Carmichael_number)
        assert!(!U64::from(561u16).is_prime_miller_rabin_vartime(&mut rng, 2));
        assert!(!U64::from(9_746_347_772_161u64).is_prime_miller_rabin_vartime(&mut rng, 2));
        // https://en.wikipedia.org/wiki/Largest_known_prime_number
        assert!(U64::from(67_280_421_310_721u64).is_prime_miller_rabin_vartime(&mut rng, 2));
        assert!(!U64::from(67_280_421_310_722u64).is_prime_miller_rabin_vartime(&mut rng, 2));
        assert!(!U64::from(67_280_421_310_723u64).is_prime_miller_rabin_vartime(&mut rng, 2));
    }

    #[cfg(feature = "rand_core")]
    #[test]
    fn test_miller_rabin_many_rounds() {
        let mut rng = rand_chacha::ChaCha8Rng::seed_from_u64(1);
        assert!(U64::from(67_280_421_310_721u64).is_prime_miller_rabin_vartime(&mut rng, 50));
    }

    #[cfg(feature = "rand_core")]
    #[should_panic(expected = "number of rounds should be greater than 0")]
    #[test]
    fn test_miller_rabin_incorrect_rounds() {
        let mut rng = rand_chacha::ChaCha8Rng::seed_from_u64(1);
        assert!(!U64::from(0u8).is_prime_miller_rabin_vartime(&mut rng, 0));
    }
}
