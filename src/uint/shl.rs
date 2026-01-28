//! [`Uint`] bitwise left shift operations.

use core::num::NonZeroU32;

use crate::{
    Choice, CtOption, Limb, Shl, ShlAssign, ShlVartime, Uint, WrappingShl,
    primitives::{u32_bits, u32_rem},
};

impl<const LIMBS: usize> Uint<LIMBS> {
    /// Computes `self << shift`.
    ///
    /// # Panics
    /// - if `shift >= Self::BITS`.
    #[inline(always)]
    #[must_use]
    #[track_caller]
    pub const fn shl(&self, shift: u32) -> Self {
        self.bounded_shl(shift, Self::BITS)
    }

    /// Computes `self << shift` in variable time.
    ///
    /// NOTE: this operation is variable time with respect to `shift` *ONLY*.
    ///
    /// When used with a fixed `shift`, this function is constant-time with respect
    /// to `self`.
    ///
    /// # Panics
    /// - if `shift >= Self::BITS`.
    #[inline(always)]
    #[must_use]
    #[track_caller]
    pub const fn shl_vartime(&self, shift: u32) -> Self {
        self.overflowing_shl_vartime(shift)
            .expect("`shift` exceeds upper bound")
    }

    /// Computes `self << shift`.
    ///
    /// Returns `None` if `shift >= Self::BITS`.
    #[inline(always)]
    #[must_use]
    pub const fn overflowing_shl(&self, shift: u32) -> CtOption<Self> {
        let in_range = Choice::from_u32_lt(shift, Self::BITS);
        let adj_shift = in_range.select_u32(0, shift);
        CtOption::new(self.shl(adj_shift), in_range)
    }

    /// Computes `self << shift`.
    ///
    /// Returns `None` if `shift >= Self::BITS`.
    ///
    /// NOTE: this operation is variable time with respect to `shift` *ONLY*.
    ///
    /// When used with a fixed `shift`, this function is constant-time with respect
    /// to `self`.
    #[inline(always)]
    #[must_use]
    pub const fn overflowing_shl_vartime(&self, shift: u32) -> Option<Self> {
        if shift < Self::BITS {
            Some(self.unbounded_shl_vartime(shift))
        } else {
            None
        }
    }

    /// Computes a left shift on a wide input as `(lo, hi)`.
    ///
    /// Returns `None` if `shift >= Self::BITS`.
    ///
    /// NOTE: this operation is variable time with respect to `shift` *ONLY*.
    ///
    /// When used with a fixed `shift`, this function is constant-time with respect
    /// to `self`.
    #[inline(always)]
    #[must_use]
    pub const fn overflowing_shl_vartime_wide(
        lower_upper: (Self, Self),
        shift: u32,
    ) -> Option<(Self, Self)> {
        let (lower, upper) = lower_upper;
        if shift >= 2 * Self::BITS {
            None
        } else if shift >= Self::BITS {
            let upper = lower.unbounded_shl_vartime(shift - Self::BITS);
            Some((Self::ZERO, upper))
        } else {
            let new_lower = lower.unbounded_shl_vartime(shift);
            let upper_lo = lower.unbounded_shr_vartime(Self::BITS - shift);
            let upper_hi = upper.unbounded_shl_vartime(shift);
            Some((new_lower, upper_lo.bitor(&upper_hi)))
        }
    }

    /// Computes `self << shift` in a panic-free manner, returning zero if the shift exceeds the
    /// precision.
    #[inline(always)]
    #[must_use]
    pub const fn unbounded_shl(&self, shift: u32) -> Self {
        ctutils::unwrap_or!(self.overflowing_shl(shift), Self::ZERO, Self::select)
    }

    /// Computes `self << shift` in variable time in a panic-free manner, returning zero if the
    /// shift exceeds the precision.
    ///
    /// NOTE: this operation is variable time with respect to `shift` *ONLY*.
    ///
    /// When used with a fixed `shift`, this function is constant-time with respect
    /// to `self`.
    #[inline(always)]
    #[must_use]
    pub const fn unbounded_shl_vartime(&self, shift: u32) -> Self {
        let res = self.unbounded_shl_by_limbs_vartime(shift / Limb::BITS);
        if let Some(rem) = NonZeroU32::new(shift % Limb::BITS) {
            res.shl_limb_nonzero_with_carry(rem, Limb::ZERO).0
        } else {
            res
        }
    }

    /// Computes `self << (shift * Limb::BITS)` in a panic-free manner, returning zero if the
    /// shift exceeds the precision.
    ///
    /// NOTE: this operation is variable time with respect to `shift` *ONLY*.
    ///
    /// When used with a fixed `shift`, this function is constant-time with respect to `self`.
    #[inline(always)]
    #[must_use]
    pub(crate) const fn unbounded_shl_by_limbs_vartime(&self, shift: u32) -> Self {
        let shift = shift as usize;
        let mut limbs = [Limb::ZERO; LIMBS];
        let mut i = shift;
        while i < LIMBS {
            limbs[i] = self.limbs[i - shift];
            i += 1;
        }
        Self { limbs }
    }

    /// Computes `self << shift` where `shift < shift_upper_bound`.
    ///
    /// The runtime is determined by `shift_upper_bound` which may be larger or smaller than
    /// `Self::BITS`.
    ///
    /// # Panics
    /// - if the shift exceeds the upper bound.
    #[must_use]
    #[track_caller]
    pub const fn bounded_shl(&self, shift: u32, shift_upper_bound: u32) -> Self {
        assert!(shift < shift_upper_bound, "`shift` exceeds upper bound");

        if shift_upper_bound <= Limb::BITS {
            self.shl_limb(shift)
        } else {
            self.bounded_shl_by_limbs(
                shift >> Limb::LOG2_BITS,
                shift_upper_bound.div_ceil(Limb::BITS),
            )
            .shl_limb(shift & (Limb::BITS - 1))
        }
    }

    /// Computes `self << (shift * Limb::BITS)` where `shift < shift_upper_bound`.
    ///
    /// The runtime is determined by `shift_upper_bound` which may be larger or smaller than
    /// `LIMBS`.
    ///
    /// # Panics
    /// - if the shift exceeds the upper bound.
    #[must_use]
    #[track_caller]
    pub(crate) const fn bounded_shl_by_limbs(&self, shift: u32, shift_upper_bound: u32) -> Self {
        assert!(shift < shift_upper_bound, "`shift` exceeds upper bound");

        let shift_bits = u32_bits(shift_upper_bound - 1);
        let mut result = *self;
        let mut i = 0;
        while i < shift_bits {
            let bit = Choice::from_u32_lsb(shift >> i);
            result = Uint::select(&result, &result.unbounded_shl_by_limbs_vartime(1 << i), bit);
            i += 1;
        }
        result
    }

    /// Computes `self << shift` in a panic-free manner, reducing shift modulo the type's width.
    #[inline(always)]
    #[must_use]
    pub const fn wrapping_shl(&self, shift: u32) -> Self {
        self.shl(u32_rem(shift, Self::BITS))
    }

    /// Computes `self << shift` in variable-time in a panic-free manner, reducing shift modulo
    /// the type's width.
    ///
    /// NOTE: this operation is variable time with respect to `shift` *ONLY*.
    ///
    /// When used with a fixed `shift`, this function is constant-time with respect to `self`.
    #[inline(always)]
    #[must_use]
    pub const fn wrapping_shl_vartime(&self, shift: u32) -> Self {
        self.unbounded_shl_vartime(shift % Self::BITS)
    }

    /// Computes `self << 1` in constant-time.
    #[inline(always)]
    #[must_use]
    pub(crate) const fn shl1(&self) -> Self {
        self.shl1_with_carry(Limb::ZERO).0
    }

    /// Computes `self << 1` in constant-time, returning the shifted result
    /// and a high carry limb.
    #[inline(always)]
    #[must_use]
    pub(crate) const fn shl1_with_carry(&self, carry: Limb) -> (Self, Limb) {
        self.shl_limb_nonzero_with_carry(NonZeroU32::MIN, carry)
    }

    /// Computes `self << shift` where `0 <= shift < Limb::BITS`,
    /// returning the result and the carry.
    ///
    /// # Panics
    /// - if `shift >= Limb::BITS`.
    #[inline(always)]
    #[must_use]
    #[track_caller]
    pub(crate) const fn shl_limb(&self, shift: u32) -> Self {
        self.shl_limb_with_carry(shift, Limb::ZERO).0
    }

    /// Computes `self << shift` where `0 <= shift < Limb::BITS`,
    /// returning the result and the carry.
    ///
    /// # Panics
    /// - if `shift >= Limb::BITS`.
    #[must_use]
    #[track_caller]
    pub(crate) const fn shl_limb_with_carry(&self, shift: u32, carry: Limb) -> (Self, Limb) {
        let nz = Choice::from_u32_nz(shift);
        let (res, carry) = self.shl_limb_nonzero_with_carry(
            NonZeroU32::new(nz.select_u32(1, shift)).expect("ensured non-zero"),
            carry,
        );
        (
            Self::select(self, &res, nz),
            Limb::select(Limb::ZERO, carry, nz),
        )
    }

    /// Computes `self << shift` where `0 < shift < Limb::BITS`,
    /// returning the result and the carry.
    ///
    /// # Panics
    /// - if `shift >= Limb::BITS`.
    #[inline(always)]
    #[must_use]
    #[track_caller]
    pub(crate) const fn shl_limb_nonzero_with_carry(
        &self,
        shift: NonZeroU32,
        mut carry: Limb,
    ) -> (Self, Limb) {
        assert!(shift.get() < Limb::BITS, "`shift` exceeds upper bound");

        let mut limbs = [Limb::ZERO; LIMBS];
        let lshift = shift.get();
        let rshift = Limb::BITS - lshift;

        let mut i = 0;
        while i < LIMBS {
            (limbs[i], carry) = (
                self.limbs[i].shl(lshift).bitor(carry),
                self.limbs[i].shr(rshift),
            );
            i += 1;
        }

        (Self { limbs }, carry)
    }
}

macro_rules! impl_shl {
    ($($shift:ty),+) => {
        $(
            impl<const LIMBS: usize> Shl<$shift> for Uint<LIMBS> {
                type Output = Uint<LIMBS>;

                #[inline]
                fn shl(self, shift: $shift) -> Uint<LIMBS> {
                    <&Self>::shl(&self, shift)
                }
            }

            impl<const LIMBS: usize> Shl<$shift> for &Uint<LIMBS> {
                type Output = Uint<LIMBS>;

                #[inline]
                fn shl(self, shift: $shift) -> Uint<LIMBS> {
                    Uint::<LIMBS>::shl(self, u32::try_from(shift).expect("invalid shift"))
                }
            }

            impl<const LIMBS: usize> ShlAssign<$shift> for Uint<LIMBS> {
                fn shl_assign(&mut self, shift: $shift) {
                    *self = self.shl(shift)
                }
            }
        )+
    };
}

impl_shl!(i32, u32, usize);

impl<const LIMBS: usize> WrappingShl for Uint<LIMBS> {
    fn wrapping_shl(&self, shift: u32) -> Uint<LIMBS> {
        self.wrapping_shl(shift)
    }
}

impl<const LIMBS: usize> ShlVartime for Uint<LIMBS> {
    fn overflowing_shl_vartime(&self, shift: u32) -> Option<Self> {
        self.overflowing_shl_vartime(shift)
    }

    fn unbounded_shl_vartime(&self, shift: u32) -> Self {
        self.unbounded_shl_vartime(shift)
    }

    fn wrapping_shl_vartime(&self, shift: u32) -> Self {
        self.wrapping_shl_vartime(shift)
    }
}

#[cfg(test)]
mod tests {
    use crate::{Limb, ShlVartime, U128, U192, U256, Uint, WrappingShl};

    const N: U256 =
        U256::from_be_hex("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141");

    const TWO_N: U256 =
        U256::from_be_hex("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFD755DB9CD5E9140777FA4BD19A06C8282");

    const FOUR_N: U256 =
        U256::from_be_hex("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFAEABB739ABD2280EEFF497A3340D90504");

    const SIXTY_FIVE: U256 =
        U256::from_be_hex("FFFFFFFFFFFFFFFD755DB9CD5E9140777FA4BD19A06C82820000000000000000");

    const EIGHTY_EIGHT: U256 =
        U256::from_be_hex("FFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD03641410000000000000000000000");

    const SIXTY_FOUR: U256 =
        U256::from_be_hex("FFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD03641410000000000000000");

    #[test]
    fn shl_simple() {
        let mut t = U256::from(1u8);
        assert_eq!(t << 1, U256::from(2u8));
        t = U256::from(3u8);
        assert_eq!(t << 8, U256::from(0x300u16));
    }

    #[test]
    fn shl1() {
        assert_eq!(N << 1, TWO_N);
        assert_eq!(N.shl1(), TWO_N);
        assert_eq!(N.shl1_with_carry(Limb::ZERO), (TWO_N, Limb::ONE));
        assert_eq!(ShlVartime::overflowing_shl_vartime(&N, 1), Some(TWO_N));
        assert_eq!(ShlVartime::unbounded_shl_vartime(&N, 1), TWO_N);
        assert_eq!(ShlVartime::wrapping_shl_vartime(&N, 1), TWO_N);
    }

    #[test]
    fn shl2() {
        assert_eq!(N << 2, FOUR_N);
    }

    #[test]
    fn shl64() {
        assert_eq!(N << 64, SIXTY_FOUR);
    }

    #[test]
    fn shl65() {
        assert_eq!(N << 65, SIXTY_FIVE);
    }

    #[test]
    fn shl88() {
        assert_eq!(N << 88, EIGHTY_EIGHT);
    }

    #[test]
    fn shl_limb() {
        let (lo, carry) = U128::ZERO.shl_limb_with_carry(16, Limb::ZERO);
        assert_eq!((lo, carry), (U128::ZERO, Limb::ZERO));
        let (lo, carry) = U128::ONE.shl_limb_with_carry(16, Limb::ZERO);
        assert_eq!((lo, carry), (U128::from_u128(0x10000), Limb::ZERO));
        let (lo, carry) = U128::MAX.shl_limb_with_carry(16, Limb::ZERO);
        assert_eq!(
            (lo, carry),
            (
                U128::from_u128(0xffffffffffffffffffffffffffff0000),
                Limb::from_u32(0xffff)
            )
        );
        let (lo, carry) = U128::MAX.shl_limb_with_carry(16, Limb::MAX);
        assert_eq!(
            (lo, carry),
            (
                U128::from_u128(0xffffffffffffffffffffffffffffffff),
                Limb::from_u32(0xffff)
            )
        );
    }

    #[test]
    fn shl_bounds() {
        assert!(N.overflowing_shl(256).is_none().to_bool_vartime());
        assert!(N.overflowing_shl_vartime(256).is_none());
        assert_eq!(N.unbounded_shl(256), Uint::ZERO);
        assert_eq!(N.unbounded_shl_vartime(256), Uint::ZERO);
        assert_eq!(N.wrapping_shl(256), N);
        assert_eq!(N.wrapping_shl_vartime(256), N);
    }

    #[test]
    #[should_panic(expected = "`shift` exceeds upper bound")]
    fn shl_bounds_panic() {
        let _ = N << 256;
    }

    #[test]
    fn shl_wide_1_1_128() {
        assert_eq!(
            Uint::overflowing_shl_vartime_wide((U128::ONE, U128::ONE), 128).unwrap(),
            (U128::ZERO, U128::ONE)
        );
        assert_eq!(
            Uint::overflowing_shl_vartime_wide((U128::ONE, U128::ONE), 128).unwrap(),
            (U128::ZERO, U128::ONE)
        );
    }

    #[test]
    fn shl_wide_max_0_1() {
        assert_eq!(
            Uint::overflowing_shl_vartime_wide((U128::MAX, U128::ZERO), 1).unwrap(),
            (U128::MAX.borrowing_sub(&U128::ONE, Limb::ZERO).0, U128::ONE)
        );
    }

    #[test]
    fn shl_wide_max_max_256() {
        assert!(Uint::overflowing_shl_vartime_wide((U128::MAX, U128::MAX), 256).is_none());
    }

    #[test]
    fn shl_by_limbs() {
        let val = Uint::<2>::from_words([1, 99]);
        assert_eq!(val.bounded_shl_by_limbs(0, 3).as_words(), &[1, 99]);
        assert_eq!(val.bounded_shl_by_limbs(1, 3).as_words(), &[0, 1]);
        assert_eq!(val.bounded_shl_by_limbs(2, 3).as_words(), &[0, 0]);
        assert_eq!(val.unbounded_shl_by_limbs_vartime(0).as_words(), &[1, 99]);
        assert_eq!(val.unbounded_shl_by_limbs_vartime(1).as_words(), &[0, 1]);
        assert_eq!(val.unbounded_shl_by_limbs_vartime(2).as_words(), &[0, 0]);
    }

    #[test]
    fn overflowing_shl() {
        assert_eq!(
            U192::ONE.overflowing_shl(2).into_option(),
            Some(U192::from_u8(4))
        );
        assert_eq!(U192::MAX.overflowing_shl(U192::BITS).into_option(), None);
        assert_eq!(
            ShlVartime::overflowing_shl_vartime(&U192::ONE, 2),
            Some(U192::from_u8(4))
        );
        assert_eq!(
            ShlVartime::overflowing_shl_vartime(&U192::MAX, U192::BITS),
            None
        );
    }

    #[test]
    fn unbounded_shl() {
        assert_eq!(U192::ONE.unbounded_shl(2), U192::from_u8(4));
        assert_eq!(U192::MAX.unbounded_shl(U192::BITS), U192::ZERO);
        assert_eq!(
            ShlVartime::unbounded_shl_vartime(&U192::ONE, 2),
            U192::from_u8(4)
        );
        assert_eq!(
            ShlVartime::unbounded_shl_vartime(&U192::MAX, U192::BITS),
            U192::ZERO
        );
    }

    #[test]
    fn wrapping_shl() {
        assert_eq!(WrappingShl::wrapping_shl(&U192::ONE, 2), U192::from_u8(4));
        assert_eq!(WrappingShl::wrapping_shl(&U192::ONE, U192::BITS), U192::ONE);
        assert_eq!(
            ShlVartime::wrapping_shl_vartime(&U192::ONE, 2),
            U192::from_u8(4)
        );
        assert_eq!(
            ShlVartime::wrapping_shl_vartime(&U192::ONE, U192::BITS),
            U192::ONE
        );
    }
}
