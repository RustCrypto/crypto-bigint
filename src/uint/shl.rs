//! [`Uint`] bitwise left shift operations.

use crate::{ConstChoice, ConstCtOption, Limb, ShlVartime, Uint, Word, WrappingShl};
use core::ops::{Shl, ShlAssign};
use subtle::CtOption;

impl<const LIMBS: usize> Uint<LIMBS> {
    /// Computes `self << shift`.
    ///
    /// Panics if `shift >= Self::BITS`.
    pub const fn shl(&self, shift: u32) -> Self {
        self.overflowing_shl(shift)
            .expect("`shift` within the bit size of the integer")
    }

    /// Computes `self << shift` in variable time.
    ///
    /// Panics if `shift >= Self::BITS`.
    pub const fn shl_vartime(&self, shift: u32) -> Self {
        self.overflowing_shl_vartime(shift)
            .expect("`shift` within the bit size of the integer")
    }

    /// Computes `self << shift`.
    ///
    /// Returns `None` if `shift >= Self::BITS`.
    pub const fn overflowing_shl(&self, shift: u32) -> ConstCtOption<Self> {
        // `floor(log2(BITS - 1))` is the number of bits in the representation of `shift`
        // (which lies in range `0 <= shift < BITS`).
        let shift_bits = u32::BITS - (Self::BITS - 1).leading_zeros();
        let overflow = ConstChoice::from_u32_lt(shift, Self::BITS).not();
        let shift = shift % Self::BITS;
        let mut result = *self;
        let mut i = 0;
        while i < shift_bits {
            let bit = ConstChoice::from_u32_lsb((shift >> i) & 1);
            result = Uint::select(
                &result,
                &result
                    .overflowing_shl_vartime(1 << i)
                    .expect("shift within range"),
                bit,
            );
            i += 1;
        }

        ConstCtOption::new(Uint::select(&result, &Self::ZERO, overflow), overflow.not())
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
    pub const fn overflowing_shl_vartime(&self, shift: u32) -> ConstCtOption<Self> {
        let mut limbs = [Limb::ZERO; LIMBS];

        if shift >= Self::BITS {
            return ConstCtOption::none(Self::ZERO);
        }

        let shift_num = (shift / Limb::BITS) as usize;
        let rem = shift % Limb::BITS;

        let mut i = shift_num;
        while i < LIMBS {
            limbs[i] = self.limbs[i - shift_num];
            i += 1;
        }

        if rem == 0 {
            return ConstCtOption::some(Self { limbs });
        }

        let mut carry = Limb::ZERO;

        let mut i = shift_num;
        while i < LIMBS {
            let shifted = limbs[i].shl(rem);
            let new_carry = limbs[i].shr(Limb::BITS - rem);
            limbs[i] = shifted.bitor(carry);
            carry = new_carry;
            i += 1;
        }

        ConstCtOption::some(Self { limbs })
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
    pub const fn overflowing_shl_vartime_wide(
        lower_upper: (Self, Self),
        shift: u32,
    ) -> ConstCtOption<(Self, Self)> {
        let (lower, upper) = lower_upper;
        if shift >= 2 * Self::BITS {
            ConstCtOption::none((Self::ZERO, Self::ZERO))
        } else if shift >= Self::BITS {
            let upper = lower
                .overflowing_shl_vartime(shift - Self::BITS)
                .expect("shift within range");
            ConstCtOption::some((Self::ZERO, upper))
        } else {
            let new_lower = lower
                .overflowing_shl_vartime(shift)
                .expect("shift within range");
            let upper_lo = lower
                .overflowing_shr_vartime(Self::BITS - shift)
                .expect("shift within range");
            let upper_hi = upper
                .overflowing_shl_vartime(shift)
                .expect("shift within range");
            ConstCtOption::some((new_lower, upper_lo.bitor(&upper_hi)))
        }
    }

    /// Computes `self << shift` in a panic-free manner, returning zero if the shift exceeds the
    /// precision.
    pub const fn wrapping_shl(&self, shift: u32) -> Self {
        self.overflowing_shl(shift).unwrap_or(Self::ZERO)
    }

    /// Computes `self << shift` in variable-time in a panic-free manner, returning zero if the
    /// shift exceeds the precision.
    pub const fn wrapping_shl_vartime(&self, shift: u32) -> Self {
        self.overflowing_shl_vartime(shift).unwrap_or(Self::ZERO)
    }

    /// Computes `self << shift` where `0 <= shift < Limb::BITS`,
    /// returning the result and the carry.
    #[inline(always)]
    pub(crate) const fn shl_limb(&self, shift: u32) -> (Self, Limb) {
        let mut limbs = [Limb::ZERO; LIMBS];

        let nz = ConstChoice::from_u32_nonzero(shift);
        let lshift = shift;
        let rshift = nz.if_true_u32(Limb::BITS - shift);
        let carry = nz.if_true_word(self.limbs[LIMBS - 1].0.wrapping_shr(Word::BITS - shift));

        limbs[0] = Limb(self.limbs[0].0 << lshift);
        let mut i = 1;
        while i < LIMBS {
            let mut limb = self.limbs[i].0 << lshift;
            let hi = self.limbs[i - 1].0 >> rshift;
            limb |= nz.if_true_word(hi);
            limbs[i] = Limb(limb);
            i += 1
        }

        (Uint::<LIMBS>::new(limbs), Limb(carry))
    }

    /// Computes `self << 1` in constant-time, returning [`ConstChoice::TRUE`]
    /// if the most significant bit was set, and [`ConstChoice::FALSE`] otherwise.
    #[inline(always)]
    pub(crate) const fn overflowing_shl1(&self) -> (Self, Limb) {
        let mut ret = Self::ZERO;
        let mut i = 0;
        let mut carry = Limb::ZERO;
        while i < LIMBS {
            let (shifted, new_carry) = self.limbs[i].shl1();
            ret.limbs[i] = shifted.bitor(carry);
            carry = new_carry;
            i += 1;
        }

        (ret, carry)
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
    fn overflowing_shl_vartime(&self, shift: u32) -> CtOption<Self> {
        self.overflowing_shl(shift).into()
    }
    fn wrapping_shl_vartime(&self, shift: u32) -> Self {
        self.wrapping_shl(shift)
    }
}

#[cfg(test)]
mod tests {
    use crate::{Limb, Uint, U128, U256};

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
        assert_eq!(N.overflowing_shl1(), (TWO_N, Limb::ONE));
    }

    #[test]
    fn shl2() {
        assert_eq!(N << 2, FOUR_N);
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
    fn shl256_const() {
        assert!(N.overflowing_shl(256).is_none().is_true_vartime());
        assert!(N.overflowing_shl_vartime(256).is_none().is_true_vartime());
    }

    #[test]
    #[should_panic(expected = "`shift` within the bit size of the integer")]
    fn shl256() {
        let _ = N << 256;
    }

    #[test]
    fn shl64() {
        assert_eq!(N << 64, SIXTY_FOUR);
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
            (U128::MAX.sbb(&U128::ONE, Limb::ZERO).0, U128::ONE)
        );
    }

    #[test]
    fn shl_wide_max_max_256() {
        assert!(
            Uint::overflowing_shl_vartime_wide((U128::MAX, U128::MAX), 256)
                .is_none()
                .is_true_vartime(),
        );
    }
}
