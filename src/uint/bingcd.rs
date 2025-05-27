//! This module implements (a constant variant of) the Optimized Extended Binary GCD algorithm,
//! which is described by Pornin as Algorithm 2 in "Optimized Binary GCD for Modular Inversion".
//! Ref: <https://eprint.iacr.org/2020/972.pdf>

use crate::Uint;

mod extension;
mod gcd;
mod matrix;
mod tools;

mod xgcd;

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
