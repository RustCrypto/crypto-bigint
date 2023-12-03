//! [`Uint`] square root operations.

use super::Uint;
use subtle::{ConstantTimeEq, CtOption};

impl<const LIMBS: usize> Uint<LIMBS> {
    /// Computes √(`self`) in constant time.
    /// Based on Brent & Zimmermann, Modern Computer Arithmetic, v0.5.9, Algorithm 1.13
    ///
    /// Callers can check if `self` is a square by squaring the result
    pub const fn sqrt(&self) -> Self {
        let max_bits = (self.bits() + 1) >> 1;
        let cap = Self::ONE.shl(max_bits);
        let mut guess = cap; // ≥ √(`self`)
        let mut xn = {
            let q = self.wrapping_div(&guess);
            let t = guess.wrapping_add(&q);
            t.shr_vartime(1)
        };

        // Repeat enough times to guarantee result has stabilized.
        // See Hast, "Note on computation of integer square roots" for a proof of this bound.
        // https://github.com/RustCrypto/crypto-bigint/files/12600669/ct_sqrt.pdf
        let mut i = 0;
        while i < Self::LOG2_BITS + 1 {
            guess = xn;
            xn = {
                let (q, _, is_some) = self.const_div_rem(&guess);
                let q = Self::ct_select(&Self::ZERO, &q, is_some);
                let t = guess.wrapping_add(&q);
                t.shr_vartime(1)
            };
            i += 1;
        }

        // at least one of `guess` and `xn` is now equal to √(`self`), so return the minimum
        Self::ct_select(&guess, &xn, Uint::ct_gt(&guess, &xn))
    }

    /// Computes √(`self`)
    /// Uses Brent & Zimmermann, Modern Computer Arithmetic, v0.5.9, Algorithm 1.13
    ///
    /// Callers can check if `self` is a square by squaring the result
    pub const fn sqrt_vartime(&self) -> Self {
        let max_bits = (self.bits_vartime() + 1) >> 1;
        let cap = Self::ONE.shl_vartime(max_bits);
        let mut guess = cap; // ≥ √(`self`)
        let mut xn = {
            let q = self.wrapping_div_vartime(&guess);
            let t = guess.wrapping_add(&q);
            t.shr_vartime(1)
        };
        // Note, xn <= guess at this point.

        // Repeat while guess decreases.
        while guess.cmp_vartime(&xn).is_gt() && !xn.cmp_vartime(&Self::ZERO).is_eq() {
            guess = xn;
            xn = {
                let q = self.wrapping_div_vartime(&guess);
                let t = guess.wrapping_add(&q);
                t.shr_vartime(1)
            };
        }

        if self.ct_is_nonzero().is_true_vartime() {
            guess
        } else {
            Self::ZERO
        }
    }

    /// Wrapped sqrt is just normal √(`self`)
    /// There’s no way wrapping could ever happen.
    /// This function exists so that all operations are accounted for in the wrapping operations.
    pub const fn wrapping_sqrt(&self) -> Self {
        self.sqrt()
    }

    /// Wrapped sqrt is just normal √(`self`)
    /// There’s no way wrapping could ever happen.
    /// This function exists so that all operations are accounted for in the wrapping operations.
    pub const fn wrapping_sqrt_vartime(&self) -> Self {
        self.sqrt_vartime()
    }

    /// Perform checked sqrt, returning a [`CtOption`] which `is_some`
    /// only if the √(`self`)² == self
    pub fn checked_sqrt(&self) -> CtOption<Self> {
        let r = self.sqrt();
        let s = r.wrapping_mul(&r);
        CtOption::new(r, ConstantTimeEq::ct_eq(self, &s))
    }

    /// Perform checked sqrt, returning a [`CtOption`] which `is_some`
    /// only if the √(`self`)² == self
    pub fn checked_sqrt_vartime(&self) -> CtOption<Self> {
        let r = self.sqrt_vartime();
        let s = r.wrapping_mul(&r);
        CtOption::new(r, ConstantTimeEq::ct_eq(self, &s))
    }
}

#[cfg(test)]
mod tests {
    use crate::{Limb, U192, U256};

    #[cfg(feature = "rand")]
    use {
        crate::{CheckedMul, Random, U512},
        rand_chacha::ChaChaRng,
        rand_core::{RngCore, SeedableRng},
    };

    #[test]
    fn edge() {
        assert_eq!(U256::ZERO.sqrt(), U256::ZERO);
        assert_eq!(U256::ONE.sqrt(), U256::ONE);
        let mut half = U256::ZERO;
        for i in 0..half.limbs.len() / 2 {
            half.limbs[i] = Limb::MAX;
        }
        assert_eq!(U256::MAX.sqrt(), half);

        assert_eq!(
            U192::from_be_hex("055fa39422bd9f281762946e056535badbf8a6864d45fa3d").sqrt(),
            U192::from_be_hex("0000000000000000000000002516f0832a538b2d98869e21")
        );

        assert_eq!(
            U256::from_be_hex("4bb750738e25a8f82940737d94a48a91f8cd918a3679ff90c1a631f2bd6c3597")
                .sqrt(),
            U256::from_be_hex("000000000000000000000000000000008b3956339e8315cff66eb6107b610075")
        );
    }

    #[test]
    fn edge_vartime() {
        assert_eq!(U256::ZERO.sqrt_vartime(), U256::ZERO);
        assert_eq!(U256::ONE.sqrt_vartime(), U256::ONE);
        let mut half = U256::ZERO;
        for i in 0..half.limbs.len() / 2 {
            half.limbs[i] = Limb::MAX;
        }
        assert_eq!(U256::MAX.sqrt_vartime(), half);
    }

    #[test]
    fn simple() {
        let tests = [
            (4u8, 2u8),
            (9, 3),
            (16, 4),
            (25, 5),
            (36, 6),
            (49, 7),
            (64, 8),
            (81, 9),
            (100, 10),
            (121, 11),
            (144, 12),
            (169, 13),
        ];
        for (a, e) in &tests {
            let l = U256::from(*a);
            let r = U256::from(*e);
            assert_eq!(l.sqrt(), r);
            assert_eq!(l.sqrt_vartime(), r);
            assert_eq!(l.checked_sqrt().is_some().unwrap_u8(), 1u8);
            assert_eq!(l.checked_sqrt_vartime().is_some().unwrap_u8(), 1u8);
        }
    }

    #[test]
    fn nonsquares() {
        assert_eq!(U256::from(2u8).sqrt(), U256::from(1u8));
        assert_eq!(U256::from(2u8).checked_sqrt().is_some().unwrap_u8(), 0);
        assert_eq!(U256::from(3u8).sqrt(), U256::from(1u8));
        assert_eq!(U256::from(3u8).checked_sqrt().is_some().unwrap_u8(), 0);
        assert_eq!(U256::from(5u8).sqrt(), U256::from(2u8));
        assert_eq!(U256::from(6u8).sqrt(), U256::from(2u8));
        assert_eq!(U256::from(7u8).sqrt(), U256::from(2u8));
        assert_eq!(U256::from(8u8).sqrt(), U256::from(2u8));
        assert_eq!(U256::from(10u8).sqrt(), U256::from(3u8));
    }

    #[test]
    fn nonsquares_vartime() {
        assert_eq!(U256::from(2u8).sqrt_vartime(), U256::from(1u8));
        assert_eq!(
            U256::from(2u8).checked_sqrt_vartime().is_some().unwrap_u8(),
            0
        );
        assert_eq!(U256::from(3u8).sqrt_vartime(), U256::from(1u8));
        assert_eq!(
            U256::from(3u8).checked_sqrt_vartime().is_some().unwrap_u8(),
            0
        );
        assert_eq!(U256::from(5u8).sqrt_vartime(), U256::from(2u8));
        assert_eq!(U256::from(6u8).sqrt_vartime(), U256::from(2u8));
        assert_eq!(U256::from(7u8).sqrt_vartime(), U256::from(2u8));
        assert_eq!(U256::from(8u8).sqrt_vartime(), U256::from(2u8));
        assert_eq!(U256::from(10u8).sqrt_vartime(), U256::from(3u8));
    }

    #[cfg(feature = "rand")]
    #[test]
    fn fuzz() {
        let mut rng = ChaChaRng::from_seed([7u8; 32]);
        for _ in 0..50 {
            let t = rng.next_u32() as u64;
            let s = U256::from(t);
            let s2 = s.checked_mul(&s).unwrap();
            assert_eq!(s2.sqrt(), s);
            assert_eq!(s2.sqrt_vartime(), s);
            assert_eq!(s2.checked_sqrt().is_some().unwrap_u8(), 1);
            assert_eq!(s2.checked_sqrt_vartime().is_some().unwrap_u8(), 1);
        }

        for _ in 0..50 {
            let s = U256::random(&mut rng);
            let mut s2 = U512::ZERO;
            s2.limbs[..s.limbs.len()].copy_from_slice(&s.limbs);
            assert_eq!(s.square().sqrt(), s2);
            assert_eq!(s.square().sqrt_vartime(), s2);
        }
    }
}
