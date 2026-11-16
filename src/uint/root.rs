//! Support for nth root calculation for [`Uint`].

use core::num::NonZeroU32;

use crate::{Limb, NonZero, Reciprocal, U64, Uint};

impl<const LIMBS: usize> Uint<LIMBS> {
    /// Computes `floor(self^(1/exp))`.
    ///
    /// Callers can check if `self` is an exact power of `exp` by exponentiating the result.
    ///
    /// This method is variable time in `self` and in the exponent.
    #[must_use]
    pub const fn floor_root_vartime(&self, exp: NonZeroU32) -> Self {
        if let Some(self_nz) = self.as_nz_vartime() {
            self_nz.floor_root_vartime(exp).get_copy()
        } else {
            Self::ZERO
        }
    }

    /// Compute the root `self^(1/exp)` returning an [`Option`] which `is_some`
    /// only if the root is exact.
    ///
    /// This method is variable time in `self` and in the exponent.
    pub fn checked_root_vartime(&self, exp: NonZeroU32) -> Option<Self> {
        if let Some(self_nz) = self.as_nz_vartime() {
            self_nz.checked_root_vartime(exp).map(NonZero::get)
        } else {
            Some(Self::ZERO)
        }
    }
}

impl<const LIMBS: usize> NonZero<Uint<LIMBS>> {
    /// Computes `floor(self^(1/exp))`.
    ///
    /// Callers can check if `self` is an exact power of `exp` by exponentiating the result.
    ///
    /// This method is variable time in self and in the exponent.
    #[must_use]
    pub const fn floor_root_vartime(&self, exp: NonZeroU32) -> Self {
        // Uses Brent & Zimmermann, Modern Computer Arithmetic, v0.5.9, Algorithm 1.14.

        if exp.get() == 1 {
            return *self;
        }
        let bits = self.as_ref().bit_width_vartime();
        if exp.get() >= bits {
            // `1 <= self < 2^exp`, so the root is 1.
            return Self::ONE;
        }
        let exp_m1 = exp.get() - 1;
        let exp_m1_limb = Limb::from_u32(exp_m1);
        let exp_recip = Reciprocal::new(NonZero::<Limb>::from_u32(exp));

        let rt_bits = bits.div_ceil(exp.get());
        // The initial guess: `x_0 = 2^ceil(b/exp)`, where `2^(b-1) <= self < 2^b`.
        // Will not overflow since `exp > 1`.
        let mut x = Uint::<LIMBS>::ZERO.set_bit_vartime(rt_bits, true);
        // Compute `self.0 / x_0^(exp-1)` by shifting. The quotient is zero if `x_0^(exp-1)`
        // exceeds the precision. The shift will not overflow since `rt_bits * exp < b + exp`.
        let mut q = self.as_ref().unbounded_shr_vartime(rt_bits * exp_m1);

        loop {
            // Calculate `x_{i+1} = floor((x_i*(exp-1) + self / x_i^(exp-1)) / exp)`, leaving `x`
            // unmodified if it would not decrease.

            // Terminate if `x_{i+1} >= x_i`, which holds exactly when `self / x_i^(exp-1) >= x_i`.
            if q.cmp_vartime(&x).is_ge() {
                return x.to_nz().expect_copied("ensured non-zero");
            }
            // Will not overflow since the numerator is less than `x_i*exp <= x_0*exp`.
            x = x
                .wrapping_mul_limb(exp_m1_limb)
                .wrapping_add(&q)
                .div_rem_limb_with_reciprocal(&exp_recip)
                .0;

            // Compute `self.0 / x_i^(exp-1)`. The quotient is zero if `x_i^(exp-1)` exceeds
            // the precision.
            let (x_pow, overflow) = x.overflowing_pow_vartime(&U64::from_u32(exp_m1));
            q = if overflow.to_bool() {
                Uint::ZERO
            } else {
                self.as_ref()
                    .div_rem_vartime(x_pow.to_nz().expect_ref("ensured non-zero"))
                    .0
            };
        }
    }

    /// Compute the root `self^(1/exp)` returning an [`Option`] which `is_some`
    /// only if the root is exact.
    ///
    /// This method is variable time in `self` and in the exponent.
    #[must_use]
    pub fn checked_root_vartime(&self, exp: NonZeroU32) -> Option<Self> {
        let r = self.floor_root_vartime(exp);
        let s = r.wrapping_pow_vartime(&U64::from_u32(exp.get()));
        if self.cmp_vartime(&s).is_eq() {
            Some(r)
        } else {
            None
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{CheckedAdd, U64, U256, Uint};
    use core::num::NonZeroU32;

    #[cfg(feature = "rand_core")]
    use {crate::Random, chacha20::ChaCha8Rng, rand_core::SeedableRng};

    #[test]
    fn floor_root_vartime_expected() {
        let three = NonZeroU32::new(3).unwrap();
        assert_eq!(U256::from(0u8).floor_root_vartime(three), U256::from(0u8));
        assert!(U256::from(0u8).checked_root_vartime(three).is_some());
        assert_eq!(U256::from(1u8).floor_root_vartime(three), U256::from(1u8));
        assert!(U256::from(1u8).checked_root_vartime(three).is_some());
        assert_eq!(U256::from(2u8).floor_root_vartime(three), U256::from(1u8));
        assert!(U256::from(2u8).checked_root_vartime(three).is_none());
        assert_eq!(U256::from(8u8).floor_root_vartime(three), U256::from(2u8));
        assert!(U256::from(8u8).checked_root_vartime(three).is_some());
        assert_eq!(U256::from(9u8).floor_root_vartime(three), U256::from(2u8));
        assert!(U256::from(9u8).checked_root_vartime(three).is_none());
    }

    /// Assert that `root` is `floor(s^(1/exp))`: `root^exp <= s < (root+1)^exp`.
    fn assert_floor_root<const LIMBS: usize>(s: Uint<LIMBS>, exp: u32) {
        let exp_nz = NonZeroU32::new(exp).unwrap();
        let exp_uint = U64::from_u32(exp);
        let root = s.floor_root_vartime(exp_nz);
        let lo = root.checked_pow_vartime(&exp_uint).into_option();
        assert!(
            lo.is_some_and(|lo| lo <= s),
            "overflow, {s} exp={exp}, root={root}"
        );
        let hi = root
            .checked_add(&Uint::ONE)
            .into_option()
            .and_then(|r| r.checked_pow_vartime(&exp_uint).into_option());
        assert!(
            hi.is_none_or(|hi| hi > s),
            "underflow, {s} exp={exp}, root={root}"
        );
        assert_eq!(
            s.checked_root_vartime(exp_nz).is_some(),
            lo == Some(s),
            "exactness, {s} exp={exp}, root={root}"
        );
    }

    #[test]
    fn floor_root_vartime_large_exp() {
        // `exp` exceeding the bit width of the input
        let exp = NonZeroU32::new(257).unwrap();
        assert_eq!(U256::from(5u8).floor_root_vartime(exp), U256::ONE);
        assert_eq!(U256::MAX.floor_root_vartime(exp), U256::ONE);
        // `x_0^(exp-1)` exceeding the precision of the input
        let exp = NonZeroU32::new(17).unwrap();
        assert_eq!(
            U256::MAX.floor_root_vartime(exp),
            U256::from(34131u32) // floor(2^(256/17))
        );
        let exp = NonZeroU32::new(u32::MAX).unwrap();
        assert_eq!(U256::MAX.floor_root_vartime(exp), U256::ONE);
        assert_eq!(U256::ONE.floor_root_vartime(exp), U256::ONE);
    }

    #[test]
    #[cfg_attr(miri, ignore)] // too slow
    fn floor_root_vartime_exhaustive_exp() {
        for exp in 1..=300 {
            assert_floor_root(U64::MAX, exp);
            assert_floor_root(U64::ONE.shl_vartime(63), exp);
            assert_floor_root(U64::from_u64(0x1234_5678_9abc_def0), exp);
            assert_floor_root(U64::from_u8(5), exp);
            assert_floor_root(U256::MAX, exp);
            assert_floor_root(U256::MAX.shr_vartime(1), exp);
            assert_floor_root(U256::ONE.shl_vartime(255), exp);
            assert_floor_root(U256::from_u8(5), exp);
        }
    }

    /// Check `a^exp - 1`, `a^exp` and `a^exp + 1` for every `exp` where `a^exp` is representable.
    fn assert_perfect_power_boundaries<const LIMBS: usize>(bases: &[u64]) {
        for &a in bases {
            let a = Uint::<LIMBS>::from_u64(a);
            for exp in 2..=Uint::<LIMBS>::BITS {
                let Some(pow) = a.checked_pow_vartime(&U64::from_u32(exp)).into_option() else {
                    break;
                };
                let exp_nz = NonZeroU32::new(exp).unwrap();
                assert_eq!(pow.floor_root_vartime(exp_nz), a, "{a}^{exp}");
                assert_eq!(pow.checked_root_vartime(exp_nz), Some(a), "{a}^{exp}");
                assert_floor_root(pow, exp);

                let below = pow.wrapping_sub(&Uint::ONE);
                assert_eq!(
                    below.floor_root_vartime(exp_nz),
                    a.wrapping_sub(&Uint::ONE),
                    "{a}^{exp} - 1"
                );
                assert_floor_root(below, exp);

                if let Some(above) = pow.checked_add(&Uint::ONE).into_option() {
                    assert_eq!(above.floor_root_vartime(exp_nz), a, "{a}^{exp} + 1");
                    assert_floor_root(above, exp);
                }
            }
        }
    }

    #[test]
    #[cfg_attr(miri, ignore)] // too slow
    fn floor_root_vartime_perfect_power_boundaries() {
        let bases = [2, 3, 4, 5, 7, 10, 15, 16, 17, 255, 256, 257, 65_535, 65_537];
        assert_perfect_power_boundaries::<{ U64::LIMBS }>(&bases);
        assert_perfect_power_boundaries::<{ U256::LIMBS }>(&bases);
        assert_perfect_power_boundaries::<{ U256::LIMBS }>(&[
            u64::from(u32::MAX),
            1 << 32,
            (1 << 32) + 1,
            u64::MAX,
        ]);
    }

    #[cfg(feature = "rand_core")]
    #[test]
    fn fuzz() {
        let mut rng: ChaCha8Rng = ChaCha8Rng::from_seed([7u8; 32]);

        for _ in 0..50 {
            let s = U256::random_from_rng(&mut rng);
            for exp in 1..10 {
                assert_floor_root(s, exp);
            }
        }
    }
}
