//! [`Uint`] bitwise right shift operations.

use crate::{ConstChoice, ConstCtOption, Limb, ShrVartime, Uint, WrappingShr};
use core::ops::{Shr, ShrAssign};
use subtle::CtOption;

impl<const LIMBS: usize> Uint<LIMBS> {
    /// Computes `self >> shift`.
    ///
    /// Panics if `shift >= Self::BITS`.
    pub const fn shr(&self, shift: u32) -> Self {
        self.overflowing_shr(shift)
            .expect("`shift` within the bit size of the integer")
    }

    /// Computes `self >> shift` in variable time.
    ///
    /// Panics if `shift >= Self::BITS`.
    pub const fn shr_vartime(&self, shift: u32) -> Self {
        self.overflowing_shr_vartime(shift)
            .expect("`shift` within the bit size of the integer")
    }

    /// Computes `self >> shift`.
    ///
    /// Returns `None` if `shift >= Self::BITS`.
    pub const fn overflowing_shr(&self, shift: u32) -> ConstCtOption<Self> {
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
                    .overflowing_shr_vartime(1 << i)
                    .expect("shift within range"),
                bit,
            );
            i += 1;
        }

        ConstCtOption::new(Uint::select(&result, &Self::ZERO, overflow), overflow.not())
    }

    /// Computes `self >> shift`.
    ///
    /// Returns `None` if `shift >= Self::BITS`.
    ///
    /// NOTE: this operation is variable time with respect to `shift` *ONLY*.
    ///
    /// When used with a fixed `shift`, this function is constant-time with respect
    /// to `self`.
    #[inline(always)]
    pub const fn overflowing_shr_vartime(&self, shift: u32) -> ConstCtOption<Self> {
        let mut limbs = [Limb::ZERO; LIMBS];

        if shift >= Self::BITS {
            return ConstCtOption::none(Self::ZERO);
        }

        let shift_num = (shift / Limb::BITS) as usize;
        let rem = shift % Limb::BITS;

        let mut i = 0;
        while i < LIMBS - shift_num {
            limbs[i] = self.limbs[i + shift_num];
            i += 1;
        }

        if rem == 0 {
            return ConstCtOption::some(Self { limbs });
        }

        let mut carry = Limb::ZERO;

        while i > 0 {
            i -= 1;
            let shifted = limbs[i].shr(rem);
            let new_carry = limbs[i].shl(Limb::BITS - rem);
            limbs[i] = shifted.bitor(carry);
            carry = new_carry;
        }

        ConstCtOption::some(Self { limbs })
    }

    /// Computes a right shift on a wide input as `(lo, hi)`.
    ///
    /// Returns `None` if `shift >= Self::BITS`.
    ///
    /// NOTE: this operation is variable time with respect to `shift` *ONLY*.
    ///
    /// When used with a fixed `shift`, this function is constant-time with respect
    /// to `self`.
    #[inline(always)]
    pub const fn overflowing_shr_vartime_wide(
        lower_upper: (Self, Self),
        shift: u32,
    ) -> ConstCtOption<(Self, Self)> {
        let (lower, upper) = lower_upper;
        if shift >= 2 * Self::BITS {
            ConstCtOption::none((Self::ZERO, Self::ZERO))
        } else if shift >= Self::BITS {
            let lower = upper
                .overflowing_shr_vartime(shift - Self::BITS)
                .expect("shift within range");
            ConstCtOption::some((lower, Self::ZERO))
        } else {
            let new_upper = upper
                .overflowing_shr_vartime(shift)
                .expect("shift within range");
            let lower_hi = upper
                .overflowing_shl_vartime(Self::BITS - shift)
                .expect("shift within range");
            let lower_lo = lower
                .overflowing_shr_vartime(shift)
                .expect("shift within range");
            ConstCtOption::some((lower_lo.bitor(&lower_hi), new_upper))
        }
    }

    /// Computes `self >> shift` in a panic-free manner, returning zero if the shift exceeds the
    /// precision.
    pub const fn wrapping_shr(&self, shift: u32) -> Self {
        self.overflowing_shr(shift).unwrap_or(Self::ZERO)
    }

    /// Computes `self >> shift` in variable-time in a panic-free manner, returning zero if the
    /// shift exceeds the precision.
    pub const fn wrapping_shr_vartime(&self, shift: u32) -> Self {
        self.overflowing_shr_vartime(shift).unwrap_or(Self::ZERO)
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

macro_rules! impl_shr {
    ($($shift:ty),+) => {
        $(
            impl<const LIMBS: usize> Shr<$shift> for Uint<LIMBS> {
                type Output = Uint<LIMBS>;

                #[inline]
                fn shr(self, shift: $shift) -> Uint<LIMBS> {
                    <&Self>::shr(&self, shift)
                }
            }

            impl<const LIMBS: usize> Shr<$shift> for &Uint<LIMBS> {
                type Output = Uint<LIMBS>;

                #[inline]
                fn shr(self, shift: $shift) -> Uint<LIMBS> {
                    Uint::<LIMBS>::shr(self, u32::try_from(shift).expect("invalid shift"))
                }
            }

            impl<const LIMBS: usize> ShrAssign<$shift> for Uint<LIMBS> {
                fn shr_assign(&mut self, shift: $shift) {
                    *self = self.shr(shift)
                }
            }
        )+
    };
}

impl_shr!(i32, u32, usize);

impl<const LIMBS: usize> WrappingShr for Uint<LIMBS> {
    fn wrapping_shr(&self, shift: u32) -> Uint<LIMBS> {
        self.wrapping_shr(shift)
    }
}

impl<const LIMBS: usize> ShrVartime for Uint<LIMBS> {
    fn overflowing_shr_vartime(&self, shift: u32) -> CtOption<Self> {
        self.overflowing_shr(shift).into()
    }
    fn wrapping_shr_vartime(&self, shift: u32) -> Self {
        self.wrapping_shr(shift)
    }
}

#[cfg(test)]
mod tests {
    use crate::{Uint, U128, U256};

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
        assert!(N.overflowing_shr(256).is_none().is_true_vartime());
        assert!(N.overflowing_shr_vartime(256).is_none().is_true_vartime());
    }

    #[test]
    #[should_panic(expected = "`shift` within the bit size of the integer")]
    fn shr256() {
        let _ = N >> 256;
    }

    #[test]
    fn shr_wide_1_1_128() {
        assert_eq!(
            Uint::overflowing_shr_vartime_wide((U128::ONE, U128::ONE), 128).unwrap(),
            (U128::ONE, U128::ZERO)
        );
    }

    #[test]
    fn shr_wide_0_max_1() {
        assert_eq!(
            Uint::overflowing_shr_vartime_wide((U128::ZERO, U128::MAX), 1).unwrap(),
            (U128::ONE << 127, U128::MAX >> 1)
        );
    }

    #[test]
    fn shr_wide_max_max_256() {
        assert!(
            Uint::overflowing_shr_vartime_wide((U128::MAX, U128::MAX), 256)
                .is_none()
                .is_true_vartime()
        );
    }
}
