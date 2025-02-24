//! [`BoxedUint`] bitwise right shift operations.

use crate::{BoxedUint, ConstantTimeSelect, Limb, ShrVartime, WrappingShr, Zero};
use core::ops::{Shr, ShrAssign};
use subtle::{Choice, ConstantTimeLess, CtOption};

impl BoxedUint {
    /// Computes `self >> shift`.
    ///
    /// Panics if `shift >= Self::BITS`.
    pub fn shr(&self, shift: u32) -> BoxedUint {
        let (result, overflow) = self.overflowing_shr(shift);
        assert!(
            !bool::from(overflow),
            "attempt to shift right with overflow"
        );
        result
    }

    /// Computes `self >>= shift`.
    ///
    /// Panics if `shift >= Self::BITS`.
    pub fn shr_assign(&mut self, shift: u32) {
        let overflow = self.overflowing_shr_assign(shift);
        assert!(
            !bool::from(overflow),
            "attempt to shift right with overflow"
        );
    }

    /// Computes `self >> shift`.
    ///
    /// Returns a zero and a truthy `Choice` if `shift >= self.bits_precision()`,
    /// or the result and a falsy `Choice` otherwise.
    pub fn overflowing_shr(&self, shift: u32) -> (Self, Choice) {
        let mut result = self.clone();
        let overflow = result.overflowing_shr_assign(shift);
        (result, overflow)
    }

    /// Computes `self >>= shift`.
    ///
    /// Returns a truthy `Choice` if `shift >= self.bits_precision()` or a falsy `Choice` otherwise.
    pub fn overflowing_shr_assign(&mut self, shift: u32) -> Choice {
        // `floor(log2(bits_precision - 1))` is the number of bits in the representation of `shift`
        // (which lies in range `0 <= shift < bits_precision`).
        let shift_bits = u32::BITS - (self.bits_precision() - 1).leading_zeros();
        let overflow = !shift.ct_lt(&self.bits_precision());
        let shift = shift % self.bits_precision();
        let mut temp = self.clone();

        for i in 0..shift_bits {
            let bit = Choice::from(((shift >> i) & 1) as u8);
            temp.set_zero();
            // Will not overflow by construction
            self.shr_vartime_into(&mut temp, 1 << i)
                .expect("shift within range");
            self.ct_assign(&temp, bit);
        }

        #[cfg(feature = "zeroize")]
        zeroize::Zeroize::zeroize(&mut temp);

        self.conditional_set_zero(overflow);
        overflow
    }

    /// Computes `self >> shift` in a panic-free manner, masking off bits of `shift` which would cause the shift to
    /// exceed the type's width.
    pub fn wrapping_shr(&self, shift: u32) -> Self {
        self.overflowing_shr(shift).0
    }

    /// Computes `self >> shift` in variable-time in a panic-free manner, masking off bits of `shift` which would cause
    /// the shift to exceed the type's width.
    pub fn wrapping_shr_vartime(&self, shift: u32) -> Self {
        let mut result = Self::zero_with_precision(self.bits_precision());
        let _ = self.shr_vartime_into(&mut result, shift);
        result
    }

    /// Computes `self >> shift`.
    /// Returns `None` if `shift >= self.bits_precision()`.
    ///
    /// WARNING: for performance reasons, `dest` is assumed to be pre-zeroized.
    ///
    /// NOTE: this operation is variable time with respect to `shift` *ONLY*.
    ///
    /// When used with a fixed `shift`, this function is constant-time with respect to `self`.
    #[inline(always)]
    fn shr_vartime_into(&self, dest: &mut Self, shift: u32) -> Option<()> {
        if shift >= self.bits_precision() {
            return None;
        }

        let nlimbs = self.nlimbs();
        let shift_num = (shift / Limb::BITS) as usize;
        let rem = shift % Limb::BITS;

        for i in 0..nlimbs - shift_num {
            dest.limbs[i] = self.limbs[i + shift_num];
        }

        if rem == 0 {
            return Some(());
        }

        for i in 0..nlimbs - shift_num - 1 {
            let shifted = dest.limbs[i].shr(rem);
            let carry = dest.limbs[i + 1].shl(Limb::BITS - rem);
            dest.limbs[i] = shifted.bitor(carry);
        }
        dest.limbs[nlimbs - shift_num - 1] = dest.limbs[nlimbs - shift_num - 1].shr(rem);

        Some(())
    }

    /// Computes `self >> shift`.
    /// Returns `None` if `shift >= self.bits_precision()`.
    ///
    /// NOTE: this operation is variable time with respect to `shift` *ONLY*.
    ///
    /// When used with a fixed `shift`, this function is constant-time with respect to `self`.
    #[inline(always)]
    pub fn shr_vartime(&self, shift: u32) -> Option<Self> {
        let mut result = Self::zero_with_precision(self.bits_precision());
        let success = self.shr_vartime_into(&mut result, shift);
        success.map(|_| result)
    }

    /// Computes `self >> 1` in constant-time, returning a true [`Choice`]
    /// if the least significant bit was set, and a false [`Choice::FALSE`] otherwise.
    pub(crate) fn shr1_with_carry(&self) -> (Self, Choice) {
        let carry = self.limbs[0].0 & 1;
        (self.shr1(), Choice::from(carry as u8))
    }

    /// Computes `self >> 1` in constant-time.
    pub(crate) fn shr1(&self) -> Self {
        let mut ret = self.clone();
        ret.shr1_assign();
        ret
    }

    /// Computes `self >> 1` in-place in constant-time.
    pub(crate) fn shr1_assign(&mut self) {
        self.limbs[0].shr_assign(1);

        for i in 1..self.limbs.len() {
            // set carry bit
            self.limbs[i - 1].0 |= (self.limbs[i].0 & 1) << Limb::HI_BIT;
            self.limbs[i].shr_assign(1);
        }
    }
}

macro_rules! impl_shr {
    ($($shift:ty),+) => {
        $(
            impl Shr<$shift> for BoxedUint {
                type Output = BoxedUint;

                #[inline]
                fn shr(self, shift: $shift) -> BoxedUint {
                    <&Self>::shr(&self, shift)
                }
            }

            impl Shr<$shift> for &BoxedUint {
                type Output = BoxedUint;

                #[inline]
                fn shr(self, shift: $shift) -> BoxedUint {
                    BoxedUint::shr(self, u32::try_from(shift).expect("invalid shift"))
                }
            }

            impl ShrAssign<$shift> for BoxedUint {
                fn shr_assign(&mut self, shift: $shift) {
                    BoxedUint::shr_assign(self, u32::try_from(shift).expect("invalid shift"))
                }
            }
        )+
    };
}

impl_shr!(i32, u32, usize);

impl WrappingShr for BoxedUint {
    fn wrapping_shr(&self, shift: u32) -> BoxedUint {
        self.wrapping_shr(shift)
    }
}

impl ShrVartime for BoxedUint {
    fn overflowing_shr_vartime(&self, shift: u32) -> CtOption<Self> {
        let (result, overflow) = self.overflowing_shr(shift);
        CtOption::new(result, !overflow)
    }
    fn wrapping_shr_vartime(&self, shift: u32) -> Self {
        self.wrapping_shr(shift)
    }
}

#[cfg(test)]
mod tests {
    use super::BoxedUint;

    #[test]
    fn shr1_assign() {
        let mut n = BoxedUint::from(0x3c442b21f19185fe433f0a65af902b8fu128);
        let n_shr1 = BoxedUint::from(0x1e221590f8c8c2ff219f8532d7c815c7u128);
        n.shr1_assign();
        assert_eq!(n, n_shr1);
    }

    #[test]
    fn shr() {
        let n = BoxedUint::from(0x80000000000000000u128);
        assert_eq!(BoxedUint::zero(), &n >> 68);
        assert_eq!(BoxedUint::one(), &n >> 67);
        assert_eq!(BoxedUint::from(2u8), &n >> 66);
        assert_eq!(BoxedUint::from(4u8), &n >> 65);
    }

    #[test]
    fn shr_vartime() {
        let n = BoxedUint::from(0x80000000000000000u128);
        assert_eq!(BoxedUint::zero(), n.shr_vartime(68).unwrap());
        assert_eq!(BoxedUint::one(), n.shr_vartime(67).unwrap());
        assert_eq!(BoxedUint::from(2u8), n.shr_vartime(66).unwrap());
        assert_eq!(BoxedUint::from(4u8), n.shr_vartime(65).unwrap());
    }
}
