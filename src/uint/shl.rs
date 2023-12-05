//! [`Uint`] bitwise left shift operations.

use crate::{CtChoice, Limb, Uint, Word};
use core::ops::{Shl, ShlAssign};

impl<const LIMBS: usize> Uint<LIMBS> {
    /// Computes `self << shift`.
    /// If `shift >= Self::BITS`, returns zero as the first tuple element,
    /// and `CtChoice::TRUE` as the second element.
    pub const fn shl(&self, shift: u32) -> (Self, CtChoice) {
        let overflow = CtChoice::from_u32_lt(shift, Self::BITS).not();
        let shift = shift % Self::BITS;
        let mut result = *self;
        let mut i = 0;
        while i < Self::LOG2_BITS + 1 {
            let bit = CtChoice::from_u32_lsb((shift >> i) & 1);
            result = Uint::ct_select(&result, &result.shl_vartime(1 << i).0, bit);
            i += 1;
        }

        (Uint::ct_select(&result, &Self::ZERO, overflow), overflow)
    }

    /// Computes `self << shift`.
    /// If `shift >= Self::BITS`, returns zero as the first tuple element,
    /// and `CtChoice::TRUE` as the second element.
    ///
    /// NOTE: this operation is variable time with respect to `shift` *ONLY*.
    ///
    /// When used with a fixed `shift`, this function is constant-time with respect
    /// to `self`.
    #[inline(always)]
    pub const fn shl_vartime(&self, shift: u32) -> (Self, CtChoice) {
        let mut limbs = [Limb::ZERO; LIMBS];

        if shift >= Self::BITS {
            return (Self::ZERO, CtChoice::TRUE);
        }

        let shift_num = (shift / Limb::BITS) as usize;
        let rem = shift % Limb::BITS;

        let mut i = LIMBS;
        while i > shift_num {
            i -= 1;
            limbs[i] = self.limbs[i - shift_num];
        }

        let (new_lower, _carry) = (Self { limbs }).shl_limb(rem);
        (new_lower, CtChoice::FALSE)
    }

    /// Computes a left shift on a wide input as `(lo, hi)`.
    /// If `shift >= Self::BITS`, returns a tuple of zeros as the first element,
    /// and `CtChoice::TRUE` as the second element.
    ///
    /// NOTE: this operation is variable time with respect to `shift` *ONLY*.
    ///
    /// When used with a fixed `shift`, this function is constant-time with respect
    /// to `self`.
    #[inline(always)]
    pub const fn shl_vartime_wide(
        lower_upper: (Self, Self),
        shift: u32,
    ) -> ((Self, Self), CtChoice) {
        let (lower, upper) = lower_upper;
        if shift >= 2 * Self::BITS {
            ((Self::ZERO, Self::ZERO), CtChoice::TRUE)
        } else if shift >= Self::BITS {
            let (upper, _) = lower.shl_vartime(shift - Self::BITS);
            ((Self::ZERO, upper), CtChoice::FALSE)
        } else {
            let (new_lower, _) = lower.shl_vartime(shift);
            let (upper_lo, _) = lower.shr_vartime(Self::BITS - shift);
            let (upper_hi, _) = upper.shl_vartime(shift);
            ((new_lower, upper_lo.bitor(&upper_hi)), CtChoice::FALSE)
        }
    }

    /// Computes `self << shift` where `0 <= shift < Limb::BITS`,
    /// returning the result and the carry.
    #[inline(always)]
    pub(crate) const fn shl_limb(&self, shift: u32) -> (Self, Limb) {
        let mut limbs = [Limb::ZERO; LIMBS];

        let nz = CtChoice::from_u32_nonzero(shift);
        let lshift = shift;
        let rshift = nz.if_true_u32(Limb::BITS - shift);
        let carry = nz.if_true_word(self.limbs[LIMBS - 1].0.wrapping_shr(Word::BITS - shift));

        let mut i = LIMBS - 1;
        while i > 0 {
            let mut limb = self.limbs[i].0 << lshift;
            let hi = self.limbs[i - 1].0 >> rshift;
            limb |= nz.if_true_word(hi);
            limbs[i] = Limb(limb);
            i -= 1
        }
        limbs[0] = Limb(self.limbs[0].0 << lshift);

        (Uint::<LIMBS>::new(limbs), Limb(carry))
    }

    /// Computes `self >> 1` in constant-time.
    pub(crate) const fn shl1(&self) -> Self {
        // TODO(tarcieri): optimized implementation
        self.shl_vartime(1).0
    }
}

impl<const LIMBS: usize> Shl<u32> for Uint<LIMBS> {
    type Output = Uint<LIMBS>;

    fn shl(self, shift: u32) -> Uint<LIMBS> {
        <&Uint<LIMBS> as Shl<u32>>::shl(&self, shift)
    }
}

impl<const LIMBS: usize> Shl<u32> for &Uint<LIMBS> {
    type Output = Uint<LIMBS>;

    fn shl(self, shift: u32) -> Uint<LIMBS> {
        let (result, overflow) = Uint::<LIMBS>::shl(self, shift);
        assert!(
            !overflow.is_true_vartime(),
            "attempt to shift left with overflow"
        );
        result
    }
}

impl<const LIMBS: usize> ShlAssign<u32> for Uint<LIMBS> {
    fn shl_assign(&mut self, shift: u32) {
        *self = self.shl(shift)
    }
}

#[cfg(test)]
mod tests {
    use crate::{CtChoice, Limb, Uint, U128, U256};

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
        assert_eq!(N.shl(256), (U256::ZERO, CtChoice::TRUE));
        assert_eq!(N.shl_vartime(256), (U256::ZERO, CtChoice::TRUE));
    }

    #[test]
    #[should_panic(expected = "attempt to shift left with overflow")]
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
            Uint::shl_vartime_wide((U128::ONE, U128::ONE), 128),
            ((U128::ZERO, U128::ONE), CtChoice::FALSE)
        );
        assert_eq!(
            Uint::shl_vartime_wide((U128::ONE, U128::ONE), 128),
            ((U128::ZERO, U128::ONE), CtChoice::FALSE)
        );
    }

    #[test]
    fn shl_wide_max_0_1() {
        assert_eq!(
            Uint::shl_vartime_wide((U128::MAX, U128::ZERO), 1),
            (
                (U128::MAX.sbb(&U128::ONE, Limb::ZERO).0, U128::ONE),
                CtChoice::FALSE
            )
        );
    }

    #[test]
    fn shl_wide_max_max_256() {
        assert_eq!(
            Uint::shl_vartime_wide((U128::MAX, U128::MAX), 256),
            ((U128::ZERO, U128::ZERO), CtChoice::TRUE)
        );
    }
}
