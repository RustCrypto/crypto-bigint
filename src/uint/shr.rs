//! [`Uint`] bitwise right shift operations.

use crate::{ConstChoice, Limb, Uint};
use core::ops::{Shr, ShrAssign};

impl<const LIMBS: usize> Uint<LIMBS> {
    /// Computes `self >> shift`.
    ///
    /// Panics if `shift >= Self::BITS`.
    pub const fn shr(&self, shift: u32) -> Self {
        let (result, overflow) = self.overflowing_shr(shift);
        assert!(
            !overflow.is_true_vartime(),
            "attempt to shift right with overflow"
        );
        result
    }

    /// Computes `self >> shift`.
    ///
    /// If `shift >= Self::BITS`, returns zero as the first tuple element,
    /// and `ConstChoice::TRUE` as the second element.
    pub const fn overflowing_shr(&self, shift: u32) -> (Self, ConstChoice) {
        // `floor(log2(BITS - 1))` is the number of bits in the representation of `shift`
        // (which lies in range `0 <= shift < BITS`).
        let shift_bits = u32::BITS - (Self::BITS - 1).leading_zeros();
        let overflow = ConstChoice::from_u32_lt(shift, Self::BITS).not();
        let shift = shift % Self::BITS;
        let mut result = *self;
        let mut i = 0;
        while i < shift_bits {
            let bit = ConstChoice::from_u32_lsb((shift >> i) & 1);
            result = Uint::select(&result, &result.overflowing_shr_vartime(1 << i).0, bit);
            i += 1;
        }

        (Uint::select(&result, &Self::ZERO, overflow), overflow)
    }

    /// Computes `self >> shift`.
    ///
    /// If `shift >= Self::BITS`, returns zero as the first tuple element,
    /// and `ConstChoice::TRUE` as the second element.
    ///
    /// NOTE: this operation is variable time with respect to `shift` *ONLY*.
    ///
    /// When used with a fixed `shift`, this function is constant-time with respect
    /// to `self`.
    #[inline(always)]
    pub const fn overflowing_shr_vartime(&self, shift: u32) -> (Self, ConstChoice) {
        let mut limbs = [Limb::ZERO; LIMBS];

        if shift >= Self::BITS {
            return (Self::ZERO, ConstChoice::TRUE);
        }

        let shift_num = (shift / Limb::BITS) as usize;
        let rem = shift % Limb::BITS;

        let mut i = 0;
        while i < LIMBS - shift_num {
            limbs[i] = self.limbs[i + shift_num];
            i += 1;
        }

        if rem == 0 {
            return (Self { limbs }, ConstChoice::FALSE);
        }

        let mut carry = Limb::ZERO;

        while i > 0 {
            i -= 1;
            let shifted = limbs[i].shr(rem);
            let new_carry = limbs[i].shl(Limb::BITS - rem);
            limbs[i] = shifted.bitor(carry);
            carry = new_carry;
        }

        (Self { limbs }, ConstChoice::FALSE)
    }

    /// Computes a right shift on a wide input as `(lo, hi)`.
    ///
    /// If `shift >= Self::BITS`, returns a tuple of zeros as the first element,
    /// and `ConstChoice::TRUE` as the second element.
    ///
    /// NOTE: this operation is variable time with respect to `shift` *ONLY*.
    ///
    /// When used with a fixed `shift`, this function is constant-time with respect
    /// to `self`.
    #[inline(always)]
    pub const fn overflowing_shr_vartime_wide(
        lower_upper: (Self, Self),
        shift: u32,
    ) -> ((Self, Self), ConstChoice) {
        let (lower, upper) = lower_upper;
        if shift >= 2 * Self::BITS {
            ((Self::ZERO, Self::ZERO), ConstChoice::TRUE)
        } else if shift >= Self::BITS {
            let (lower, _) = upper.overflowing_shr_vartime(shift - Self::BITS);
            ((lower, Self::ZERO), ConstChoice::FALSE)
        } else {
            let (new_upper, _) = upper.overflowing_shr_vartime(shift);
            let (lower_hi, _) = upper.overflowing_shl_vartime(Self::BITS - shift);
            let (lower_lo, _) = lower.overflowing_shr_vartime(shift);
            ((lower_lo.bitor(&lower_hi), new_upper), ConstChoice::FALSE)
        }
    }

    /// Computes `self >> 1` in constant-time.
    pub(crate) const fn shr1(&self) -> Self {
        self.shr1_with_carry().0
    }

    /// Computes `self >> 1` in constant-time, returning [`ConstChoice::TRUE`]
    /// if the least significant bit was set, and [`ConstChoice::FALSE`] otherwise.
    #[inline(always)]
    pub(crate) const fn shr1_with_carry(&self) -> (Self, ConstChoice) {
        let mut ret = Self::ZERO;
        let mut i = LIMBS;
        let mut carry = Limb::ZERO;
        while i > 0 {
            i -= 1;
            let (shifted, new_carry) = self.limbs[i].shr1();
            ret.limbs[i] = shifted.bitor(carry);
            carry = new_carry;
        }

        (ret, ConstChoice::from_word_lsb(carry.0 >> Limb::HI_BIT))
    }
}

impl<const LIMBS: usize> Shr<u32> for Uint<LIMBS> {
    type Output = Uint<LIMBS>;

    fn shr(self, shift: u32) -> Uint<LIMBS> {
        <&Uint<LIMBS> as Shr<u32>>::shr(&self, shift)
    }
}

impl<const LIMBS: usize> Shr<u32> for &Uint<LIMBS> {
    type Output = Uint<LIMBS>;

    fn shr(self, shift: u32) -> Uint<LIMBS> {
        Uint::<LIMBS>::shr(self, shift)
    }
}

impl<const LIMBS: usize> ShrAssign<u32> for Uint<LIMBS> {
    fn shr_assign(&mut self, shift: u32) {
        *self = self.shr(shift);
    }
}

#[cfg(test)]
mod tests {
    use crate::{ConstChoice, Uint, U128, U256};

    const N: U256 =
        U256::from_be_hex("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141");

    const N_2: U256 =
        U256::from_be_hex("7FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF5D576E7357A4501DDFE92F46681B20A0");

    #[test]
    fn shr1() {
        assert_eq!(N.shr1(), N_2);
        assert_eq!(N >> 1, N_2);
    }

    #[test]
    fn shr256_const() {
        assert_eq!(N.overflowing_shr(256), (U256::ZERO, ConstChoice::TRUE));
        assert_eq!(
            N.overflowing_shr_vartime(256),
            (U256::ZERO, ConstChoice::TRUE)
        );
    }

    #[test]
    #[should_panic(expected = "attempt to shift right with overflow")]
    fn shr256() {
        let _ = N >> 256;
    }

    #[test]
    fn shr_wide_1_1_128() {
        assert_eq!(
            Uint::overflowing_shr_vartime_wide((U128::ONE, U128::ONE), 128),
            ((U128::ONE, U128::ZERO), ConstChoice::FALSE)
        );
    }

    #[test]
    fn shr_wide_0_max_1() {
        assert_eq!(
            Uint::overflowing_shr_vartime_wide((U128::ZERO, U128::MAX), 1),
            ((U128::ONE << 127, U128::MAX >> 1), ConstChoice::FALSE)
        );
    }

    #[test]
    fn shr_wide_max_max_256() {
        assert_eq!(
            Uint::overflowing_shr_vartime_wide((U128::MAX, U128::MAX), 256),
            ((U128::ZERO, U128::ZERO), ConstChoice::TRUE)
        );
    }
}
