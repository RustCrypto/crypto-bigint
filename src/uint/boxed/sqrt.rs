//! [`BoxedUint`] square root operations.

use subtle::{ConstantTimeEq, ConstantTimeGreater, CtOption};

use crate::{BitOps, BoxedUint, ConstantTimeSelect, NonZero, SquareRoot};

impl BoxedUint {
    /// Computes √(`self`) in constant time.
    ///
    /// Callers can check if `self` is a square by squaring the result
    pub fn sqrt(&self) -> Self {
        // Uses Brent & Zimmermann, Modern Computer Arithmetic, v0.5.9, Algorithm 1.13.
        //
        // See Hast, "Note on computation of integer square roots"
        // for the proof of the sufficiency of the bound on iterations.
        // https://github.com/RustCrypto/crypto-bigint/files/12600669/ct_sqrt.pdf

        // The initial guess: `x_0 = 2^ceil(b/2)`, where `2^(b-1) <= self < b`.
        // Will not overflow since `b <= BITS`.
        let (mut x, _overflow) =
            Self::one_with_precision(self.bits_precision()).overflowing_shl((self.bits() + 1) >> 1); // ≥ √(`self`)

        // Repeat enough times to guarantee result has stabilized.
        let mut i = 0;
        let mut x_prev = x.clone(); // keep the previous iteration in case we need to roll back.

        // TODO (#378): the tests indicate that just `Self::LOG2_BITS` may be enough.
        while i < self.log2_bits() + 2 {
            x_prev.limbs.clone_from_slice(&x.limbs);

            // Calculate `x_{i+1} = floor((x_i + self / x_i) / 2)`

            let (nz_x, is_nonzero) = (NonZero(x.clone()), x.is_nonzero());
            let (q, _) = self.div_rem(&nz_x);

            // A protection in case `self == 0`, which will make `x == 0`
            let q = Self::ct_select(
                &Self::zero_with_precision(self.bits_precision()),
                &q,
                is_nonzero,
            );

            x = x.wrapping_add(&q).shr1();
            i += 1;
        }

        // At this point `x_prev == x_{n}` and `x == x_{n+1}`
        // where `n == i - 1 == LOG2_BITS + 1 == floor(log2(BITS)) + 1`.
        // Thus, according to Hast, `sqrt(self) = min(x_n, x_{n+1})`.
        Self::ct_select(&x_prev, &x, Self::ct_gt(&x_prev, &x))
    }

    /// Computes √(`self`)
    ///
    /// Callers can check if `self` is a square by squaring the result
    pub fn sqrt_vartime(&self) -> Self {
        // Uses Brent & Zimmermann, Modern Computer Arithmetic, v0.5.9, Algorithm 1.13

        // The initial guess: `x_0 = 2^ceil(b/2)`, where `2^(b-1) <= self < b`.
        // Will not overflow since `b <= BITS`.
        let (mut x, _overflow) =
            Self::one_with_precision(self.bits_precision()).overflowing_shl((self.bits() + 1) >> 1); // ≥ √(`self`)

        // Stop right away if `x` is zero to avoid divizion by zero.
        while !x
            .cmp_vartime(&Self::zero_with_precision(self.bits_precision()))
            .is_eq()
        {
            // Calculate `x_{i+1} = floor((x_i + self / x_i) / 2)`
            let q =
                self.wrapping_div_vartime(&NonZero::<Self>::new(x.clone()).expect("Division by 0"));
            let t = x.wrapping_add(&q);
            let next_x = t.shr1();

            // If `next_x` is the same as `x` or greater, we reached convergence
            // (`x` is guaranteed to either go down or oscillate between
            // `sqrt(self)` and `sqrt(self) + 1`)
            if !x.cmp_vartime(&next_x).is_gt() {
                break;
            }

            x = next_x;
        }

        if self.is_nonzero().into() {
            x
        } else {
            Self::zero_with_precision(self.bits_precision())
        }
    }

    /// Wrapped sqrt is just normal √(`self`)
    /// There’s no way wrapping could ever happen.
    /// This function exists so that all operations are accounted for in the wrapping operations.
    pub fn wrapping_sqrt(&self) -> Self {
        self.sqrt()
    }

    /// Wrapped sqrt is just normal √(`self`)
    /// There’s no way wrapping could ever happen.
    /// This function exists so that all operations are accounted for in the wrapping operations.
    pub fn wrapping_sqrt_vartime(&self) -> Self {
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

impl SquareRoot for BoxedUint {
    fn sqrt(&self) -> Self {
        self.sqrt()
    }

    fn sqrt_vartime(&self) -> Self {
        self.sqrt_vartime()
    }
}

#[cfg(test)]
mod tests {
    use crate::{BoxedUint, Limb};

    #[cfg(feature = "rand")]
    use {
        crate::{CheckedMul, RandomBits},
        rand_chacha::ChaChaRng,
        rand_core::{RngCore, SeedableRng},
    };

    #[test]
    fn edge() {
        assert_eq!(
            BoxedUint::zero_with_precision(256).sqrt(),
            BoxedUint::zero_with_precision(256)
        );
        assert_eq!(
            BoxedUint::one_with_precision(256).sqrt(),
            BoxedUint::one_with_precision(256)
        );
        let mut half = BoxedUint::zero_with_precision(256);
        for i in 0..half.limbs.len() / 2 {
            half.limbs[i] = Limb::MAX;
        }
        let u256_max = !BoxedUint::zero_with_precision(256);
        assert_eq!(u256_max.sqrt(), half);

        // Test edge cases that use up the maximum number of iterations.

        // `x = (r + 1)^2 - 583`, where `r` is the expected square root.
        assert_eq!(
            BoxedUint::from_be_hex("055fa39422bd9f281762946e056535badbf8a6864d45fa3d", 192)
                .unwrap()
                .sqrt(),
            BoxedUint::from_be_hex("0000000000000000000000002516f0832a538b2d98869e21", 192)
                .unwrap(),
        );
        assert_eq!(
            BoxedUint::from_be_hex("055fa39422bd9f281762946e056535badbf8a6864d45fa3d", 192)
                .unwrap()
                .sqrt_vartime(),
            BoxedUint::from_be_hex("0000000000000000000000002516f0832a538b2d98869e21", 192)
                .unwrap()
        );

        // `x = (r + 1)^2 - 205`, where `r` is the expected square root.
        assert_eq!(
            BoxedUint::from_be_hex(
                "4bb750738e25a8f82940737d94a48a91f8cd918a3679ff90c1a631f2bd6c3597",
                256
            )
            .unwrap()
            .sqrt(),
            BoxedUint::from_be_hex(
                "000000000000000000000000000000008b3956339e8315cff66eb6107b610075",
                256
            )
            .unwrap()
        );
        assert_eq!(
            BoxedUint::from_be_hex(
                "4bb750738e25a8f82940737d94a48a91f8cd918a3679ff90c1a631f2bd6c3597",
                256
            )
            .unwrap()
            .sqrt_vartime(),
            BoxedUint::from_be_hex(
                "000000000000000000000000000000008b3956339e8315cff66eb6107b610075",
                256
            )
            .unwrap()
        );
    }

    #[test]
    fn edge_vartime() {
        assert_eq!(
            BoxedUint::zero_with_precision(256).sqrt_vartime(),
            BoxedUint::zero_with_precision(256)
        );
        assert_eq!(
            BoxedUint::one_with_precision(256).sqrt_vartime(),
            BoxedUint::one_with_precision(256)
        );
        let mut half = BoxedUint::zero_with_precision(256);
        for i in 0..half.limbs.len() / 2 {
            half.limbs[i] = Limb::MAX;
        }
        let u256_max = !BoxedUint::zero_with_precision(256);
        assert_eq!(u256_max.sqrt_vartime(), half);
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
            let l = BoxedUint::from(*a);
            let r = BoxedUint::from(*e);
            assert_eq!(l.sqrt(), r);
            assert_eq!(l.sqrt_vartime(), r);
            assert_eq!(l.checked_sqrt().is_some().unwrap_u8(), 1u8);
            assert_eq!(l.checked_sqrt_vartime().is_some().unwrap_u8(), 1u8);
        }
    }

    #[test]
    fn nonsquares() {
        assert_eq!(BoxedUint::from(2u8).sqrt(), BoxedUint::from(1u8));
        assert_eq!(BoxedUint::from(2u8).checked_sqrt().is_some().unwrap_u8(), 0);
        assert_eq!(BoxedUint::from(3u8).sqrt(), BoxedUint::from(1u8));
        assert_eq!(BoxedUint::from(3u8).checked_sqrt().is_some().unwrap_u8(), 0);
        assert_eq!(BoxedUint::from(5u8).sqrt(), BoxedUint::from(2u8));
        assert_eq!(BoxedUint::from(6u8).sqrt(), BoxedUint::from(2u8));
        assert_eq!(BoxedUint::from(7u8).sqrt(), BoxedUint::from(2u8));
        assert_eq!(BoxedUint::from(8u8).sqrt(), BoxedUint::from(2u8));
        assert_eq!(BoxedUint::from(10u8).sqrt(), BoxedUint::from(3u8));
    }

    #[test]
    fn nonsquares_vartime() {
        assert_eq!(BoxedUint::from(2u8).sqrt_vartime(), BoxedUint::from(1u8));
        assert_eq!(
            BoxedUint::from(2u8)
                .checked_sqrt_vartime()
                .is_some()
                .unwrap_u8(),
            0
        );
        assert_eq!(BoxedUint::from(3u8).sqrt_vartime(), BoxedUint::from(1u8));
        assert_eq!(
            BoxedUint::from(3u8)
                .checked_sqrt_vartime()
                .is_some()
                .unwrap_u8(),
            0
        );
        assert_eq!(BoxedUint::from(5u8).sqrt_vartime(), BoxedUint::from(2u8));
        assert_eq!(BoxedUint::from(6u8).sqrt_vartime(), BoxedUint::from(2u8));
        assert_eq!(BoxedUint::from(7u8).sqrt_vartime(), BoxedUint::from(2u8));
        assert_eq!(BoxedUint::from(8u8).sqrt_vartime(), BoxedUint::from(2u8));
        assert_eq!(BoxedUint::from(10u8).sqrt_vartime(), BoxedUint::from(3u8));
    }

    #[cfg(feature = "rand")]
    #[test]
    fn fuzz() {
        let mut rng = ChaChaRng::from_seed([7u8; 32]);
        for _ in 0..50 {
            let t = rng.next_u32() as u64;
            let s = BoxedUint::from(t);
            let s2 = s.checked_mul(&s).unwrap();
            assert_eq!(s2.sqrt(), s);
            assert_eq!(s2.sqrt_vartime(), s);
            assert_eq!(s2.checked_sqrt().is_some().unwrap_u8(), 1);
            assert_eq!(s2.checked_sqrt_vartime().is_some().unwrap_u8(), 1);
        }

        for _ in 0..50 {
            let s = BoxedUint::random_bits(&mut rng, 512);
            let mut s2 = BoxedUint::zero_with_precision(512);
            s2.limbs[..s.limbs.len()].copy_from_slice(&s.limbs);
            assert_eq!(s.square().sqrt(), s2);
            assert_eq!(s.square().sqrt_vartime(), s2);
        }
    }
}
