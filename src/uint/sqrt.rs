//! [`Uint`] square root operations.

use crate::{CtEq, CtOption, Limb, NonZero, SquareRoot, Uint};

impl<const LIMBS: usize> Uint<LIMBS> {
    /// Computes √(`self`) in constant time.
    ///
    /// Callers can check if `self` is a square by squaring the result
    pub const fn sqrt(&self) -> Self {
        let self_is_nz = self.is_nonzero();
        let root_nz = NonZero(Self::select(&Self::ONE, self, self_is_nz))
            .sqrt()
            .get_copy();
        Self::select(&Self::ZERO, &root_nz, self_is_nz)
    }

    /// Computes √(`self`)
    ///
    /// Callers can check if `self` is a square by squaring the result.
    ///
    /// Variable time with respect to `self`.
    pub const fn sqrt_vartime(&self) -> Self {
        // Uses Brent & Zimmermann, Modern Computer Arithmetic, v0.5.9, Algorithm 1.13

        let bits = self.bits_vartime();
        if bits <= Limb::BITS {
            let rt = self.limbs[0].0.isqrt();
            return Self::from_word(rt);
        }
        let rt_bits = bits.div_ceil(2);

        // The initial guess: `x_0 = 2^ceil(b/2)`, where `2^(b-1) <= self < b`.
        // Will not overflow since `b <= BITS`.
        let mut x = Self::ZERO.set_bit_vartime(rt_bits, true);
        // Compute `self / x_0` by shifting.
        let mut q = self.shr_vartime(rt_bits);

        loop {
            // Terminate if `x_{i+1}` >= `x`.
            if q.cmp_vartime(&x).is_ge() {
                return x;
            }
            // Calculate `x_{i+1} = floor((x_i + self / x_i) / 2)`
            x = x.wrapping_add(&q).shr_vartime(1);
            q = self.wrapping_div_vartime(x.to_nz().expect_ref("ensured non-zero"));
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
        let s = r.wrapping_square();
        CtOption::new(r, self.ct_eq(&s))
    }

    /// Perform checked sqrt, returning a [`CtOption`] which `is_some`
    /// only if the √(`self`)² == self
    pub fn checked_sqrt_vartime(&self) -> CtOption<Self> {
        let r = self.sqrt_vartime();
        let s = r.wrapping_square();
        CtOption::new(r, self.ct_eq(&s))
    }
}

impl<const LIMBS: usize> NonZero<Uint<LIMBS>> {
    /// Computes √(`self`) in constant time.
    ///
    /// Callers can check if `self` is a square by squaring the result
    pub const fn sqrt(&self) -> Self {
        // Uses Brent & Zimmermann, Modern Computer Arithmetic, v0.5.9, Algorithm 1.13.
        //
        // See Hast, "Note on computation of integer square roots"
        // for the proof of the sufficiency of the bound on iterations.
        // https://github.com/RustCrypto/crypto-bigint/files/12600669/ct_sqrt.pdf

        let rt_bits = self.0.bits().div_ceil(2);
        // The initial guess: `x_0 = 2^ceil(b/2)`, where `2^(b-1) <= self < 2^b`.
        // Will not overflow since `b <= BITS`.
        let mut x = Uint::<LIMBS>::ZERO.set_bit_vartime(rt_bits, true);
        // Compute `self.0 / x_0` by shifting.
        let mut q = self.0.shr(rt_bits);
        // The first division has been performed.
        let mut i = 1;

        loop {
            // Calculate `x_{i+1} = floor((x_i + self_nz / x_i) / 2)`, leaving `x` unmodified
            // if it would increase.
            x = Uint::select(&x.wrapping_add(&q).shr1(), &x, Uint::lt(&x, &q));

            // We repeat enough times to guarantee the result has stabilized.
            // TODO (#378): the tests indicate that just `Self::LOG2_BITS` may be enough.
            i += 1;
            if i >= Uint::<LIMBS>::LOG2_BITS + 2 {
                return x.to_nz().expect_copied("ensured non-zero");
            }

            (q, _) = self.0.div_rem(x.to_nz().expect_ref("ensured non-zero"));
        }
    }
}

impl<const LIMBS: usize> SquareRoot for Uint<LIMBS> {
    fn sqrt(&self) -> Self {
        self.sqrt()
    }

    fn sqrt_vartime(&self) -> Self {
        self.sqrt_vartime()
    }
}

impl<const LIMBS: usize> SquareRoot for NonZero<Uint<LIMBS>> {
    fn sqrt(&self) -> Self {
        self.sqrt()
    }

    fn sqrt_vartime(&self) -> Self {
        self.0
            .sqrt_vartime()
            .to_nz()
            .expect_copied("ensured non-zero")
    }
}

#[cfg(test)]
mod tests {
    use crate::{Limb, U192, U256};

    #[cfg(feature = "rand_core")]
    use {
        crate::{Random, U512},
        chacha20::ChaCha8Rng,
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

        // Test edge cases that use up the maximum number of iterations.

        // `x = (r + 1)^2 - 583`, where `r` is the expected square root.
        assert_eq!(
            U192::from_be_hex("055fa39422bd9f281762946e056535badbf8a6864d45fa3d").sqrt(),
            U192::from_be_hex("0000000000000000000000002516f0832a538b2d98869e21")
        );
        assert_eq!(
            U192::from_be_hex("055fa39422bd9f281762946e056535badbf8a6864d45fa3d").sqrt_vartime(),
            U192::from_be_hex("0000000000000000000000002516f0832a538b2d98869e21")
        );

        // `x = (r + 1)^2 - 205`, where `r` is the expected square root.
        assert_eq!(
            U256::from_be_hex("4bb750738e25a8f82940737d94a48a91f8cd918a3679ff90c1a631f2bd6c3597")
                .sqrt(),
            U256::from_be_hex("000000000000000000000000000000008b3956339e8315cff66eb6107b610075")
        );
        assert_eq!(
            U256::from_be_hex("4bb750738e25a8f82940737d94a48a91f8cd918a3679ff90c1a631f2bd6c3597")
                .sqrt_vartime(),
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
            assert!(l.checked_sqrt().is_some().to_bool());
            assert!(l.checked_sqrt_vartime().is_some().to_bool());
        }
    }

    #[test]
    fn nonsquares() {
        assert_eq!(U256::from(2u8).sqrt(), U256::from(1u8));
        assert!(!U256::from(2u8).checked_sqrt().is_some().to_bool());
        assert_eq!(U256::from(3u8).sqrt(), U256::from(1u8));
        assert!(!U256::from(3u8).checked_sqrt().is_some().to_bool());
        assert_eq!(U256::from(5u8).sqrt(), U256::from(2u8));
        assert_eq!(U256::from(6u8).sqrt(), U256::from(2u8));
        assert_eq!(U256::from(7u8).sqrt(), U256::from(2u8));
        assert_eq!(U256::from(8u8).sqrt(), U256::from(2u8));
        assert_eq!(U256::from(10u8).sqrt(), U256::from(3u8));
    }

    #[test]
    fn nonsquares_vartime() {
        assert_eq!(U256::from(2u8).sqrt_vartime(), U256::from(1u8));
        assert!(!U256::from(2u8).checked_sqrt_vartime().is_some().to_bool());
        assert_eq!(U256::from(3u8).sqrt_vartime(), U256::from(1u8));
        assert!(!U256::from(3u8).checked_sqrt_vartime().is_some().to_bool());
        assert_eq!(U256::from(5u8).sqrt_vartime(), U256::from(2u8));
        assert_eq!(U256::from(6u8).sqrt_vartime(), U256::from(2u8));
        assert_eq!(U256::from(7u8).sqrt_vartime(), U256::from(2u8));
        assert_eq!(U256::from(8u8).sqrt_vartime(), U256::from(2u8));
        assert_eq!(U256::from(10u8).sqrt_vartime(), U256::from(3u8));
    }

    #[cfg(feature = "rand_core")]
    #[test]
    fn fuzz() {
        let mut rng = ChaCha8Rng::from_seed([7u8; 32]);
        for _ in 0..50 {
            let t = rng.next_u32() as u64;
            let s = U256::from(t);
            let s2 = s.checked_mul(&s).unwrap();
            assert_eq!(s2.sqrt(), s);
            assert_eq!(s2.sqrt_vartime(), s);
            assert!(s2.checked_sqrt().is_some().to_bool());
            assert!(s2.checked_sqrt_vartime().is_some().to_bool());
        }

        for _ in 0..50 {
            let s = U256::random_from_rng(&mut rng);
            let mut s2 = U512::ZERO;
            s2.limbs[..s.limbs.len()].copy_from_slice(&s.limbs);
            assert_eq!(s.square().sqrt(), s2);
            assert_eq!(s.square().sqrt_vartime(), s2);
        }
    }
}
