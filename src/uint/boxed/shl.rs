//! [`BoxedUint`] bitwise left shift operations.

use crate::{
    BoxedUint, ConstChoice, ConstantTimeSelect, Limb, ShlVartime, Word, WrappingShl, Zero,
};
use core::ops::{Shl, ShlAssign};
use subtle::{Choice, ConstantTimeLess, CtOption};

impl BoxedUint {
    /// Computes `self << shift`.
    ///
    /// Panics if `shift >= Self::BITS`.
    pub fn shl(&self, shift: u32) -> BoxedUint {
        let (result, overflow) = self.overflowing_shl(shift);
        assert!(!bool::from(overflow), "attempt to shift left with overflow");
        result
    }

    /// Computes `self <<= shift`.
    ///
    /// Panics if `shift >= Self::BITS`.
    pub fn shl_assign(&mut self, shift: u32) {
        let overflow = self.overflowing_shl_assign(shift);
        assert!(!bool::from(overflow), "attempt to shift left with overflow");
    }

    /// Computes `self << shift`.
    ///
    /// Returns a zero and a truthy `Choice` if `shift >= self.bits_precision()`,
    /// or the result and a falsy `Choice` otherwise.
    pub fn overflowing_shl(&self, shift: u32) -> (Self, Choice) {
        let mut result = self.clone();
        let overflow = result.overflowing_shl_assign(shift);
        (result, overflow)
    }

    /// Computes `self <<= shift`.
    ///
    /// Returns a truthy `Choice` if `shift >= self.bits_precision()` or a falsy `Choice` otherwise.
    pub fn overflowing_shl_assign(&mut self, shift: u32) -> Choice {
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
            self.shl_vartime_into(&mut temp, 1 << i)
                .expect("shift within range");
            self.ct_assign(&temp, bit);
        }

        #[cfg(feature = "zeroize")]
        zeroize::Zeroize::zeroize(&mut temp);

        self.conditional_set_zero(overflow);
        overflow
    }

    /// Computes `self << shift` in a panic-free manner, masking off bits of `shift` which would cause the shift to
    /// exceed the type's width.
    pub fn wrapping_shl(&self, shift: u32) -> Self {
        self.overflowing_shl(shift).0
    }

    /// Computes `self << shift` in variable-time in a panic-free manner, masking off bits of `shift` which would cause
    /// the shift to exceed the type's width.
    pub fn wrapping_shl_vartime(&self, shift: u32) -> Self {
        let mut result = Self::zero_with_precision(self.bits_precision());
        let _ = self.shl_vartime_into(&mut result, shift);
        result
    }

    /// Computes `self << shift` and writes the result into `dest`.
    /// Returns `None` if `shift >= self.bits_precision()`.
    ///
    /// WARNING: for performance reasons, `dest` is assumed to be pre-zeroized.
    ///
    /// NOTE: this operation is variable time with respect to `shift` *ONLY*.
    ///
    /// When used with a fixed `shift`, this function is constant-time with respect to `self`.
    #[inline(always)]
    fn shl_vartime_into(&self, dest: &mut Self, shift: u32) -> Option<()> {
        if shift >= self.bits_precision() {
            return None;
        }

        let nlimbs = self.nlimbs();
        let shift_num = (shift / Limb::BITS) as usize;
        let rem = shift % Limb::BITS;

        for i in shift_num..nlimbs {
            dest.limbs[i] = self.limbs[i - shift_num];
        }

        if rem == 0 {
            return Some(());
        }

        let mut carry = Limb::ZERO;

        for i in shift_num..nlimbs {
            let shifted = dest.limbs[i].shl(rem);
            let new_carry = dest.limbs[i].shr(Limb::BITS - rem);
            dest.limbs[i] = shifted.bitor(carry);
            carry = new_carry;
        }

        Some(())
    }

    /// Computes `self << shift`.
    /// Returns `None` if `shift >= self.bits_precision()`.
    ///
    /// NOTE: this operation is variable time with respect to `shift` *ONLY*.
    ///
    /// When used with a fixed `shift`, this function is constant-time with respect to `self`.
    #[inline(always)]
    pub fn shl_vartime(&self, shift: u32) -> Option<Self> {
        let mut result = Self::zero_with_precision(self.bits_precision());
        let success = self.shl_vartime_into(&mut result, shift);
        success.map(|_| result)
    }

    /// Computes `self << 1` in constant-time.
    pub(crate) fn overflowing_shl1(&self) -> (Self, Limb) {
        let mut ret = self.clone();
        let carry = ret.shl1_assign();
        (ret, carry)
    }

    /// Computes `self << 1` in-place in constant-time.
    pub(crate) fn shl1_assign(&mut self) -> Limb {
        let mut carry = self.limbs[0] >> Limb::HI_BIT;
        self.limbs[0].shl_assign(1);
        for i in 1..self.limbs.len() {
            (self.limbs[i], carry) = ((self.limbs[i] << 1) | carry, self.limbs[i] >> Limb::HI_BIT);
        }
        carry
    }

    /// Computes `self << shift` where `0 <= shift < Limb::BITS`,
    /// returning the result and the carry.
    pub(crate) fn shl_limb(&self, shift: u32) -> (Self, Limb) {
        let mut limbs = vec![Limb::ZERO; self.limbs.len()];

        let nz = ConstChoice::from_u32_nonzero(shift);
        let lshift = shift;
        let rshift = nz.if_true_u32(Limb::BITS - shift);
        let carry = nz.if_true_word(
            self.limbs[self.limbs.len() - 1]
                .0
                .wrapping_shr(Word::BITS - shift),
        );

        limbs[0] = Limb(self.limbs[0].0 << lshift);
        let mut i = 1;
        while i < self.limbs.len() {
            let mut limb = self.limbs[i].0 << lshift;
            let hi = self.limbs[i - 1].0 >> rshift;
            limb |= nz.if_true_word(hi);
            limbs[i] = Limb(limb);
            i += 1
        }

        (
            BoxedUint {
                limbs: limbs.into(),
            },
            Limb(carry),
        )
    }
}

macro_rules! impl_shl {
    ($($shift:ty),+) => {
        $(
            impl Shl<$shift> for BoxedUint {
                type Output = BoxedUint;

                #[inline]
                fn shl(self, shift: $shift) -> BoxedUint {
                    <&Self>::shl(&self, shift)
                }
            }

            impl Shl<$shift> for &BoxedUint {
                type Output = BoxedUint;

                #[inline]
                fn shl(self, shift: $shift) -> BoxedUint {
                    BoxedUint::shl(self, u32::try_from(shift).expect("invalid shift"))
                }
            }

            impl ShlAssign<$shift> for BoxedUint {
                fn shl_assign(&mut self, shift: $shift) {
                    BoxedUint::shl_assign(self, u32::try_from(shift).expect("invalid shift"))
                }
            }
        )+
    };
}

impl_shl!(i32, u32, usize);

impl WrappingShl for BoxedUint {
    fn wrapping_shl(&self, shift: u32) -> BoxedUint {
        self.wrapping_shl(shift)
    }
}

impl ShlVartime for BoxedUint {
    fn overflowing_shl_vartime(&self, shift: u32) -> CtOption<Self> {
        let (result, overflow) = self.overflowing_shl(shift);
        CtOption::new(result, !overflow)
    }
    fn wrapping_shl_vartime(&self, shift: u32) -> Self {
        self.wrapping_shl(shift)
    }
}

#[cfg(test)]
mod tests {
    use super::BoxedUint;

    #[test]
    fn shl() {
        let one = BoxedUint::one_with_precision(128);

        assert_eq!(BoxedUint::from(2u8), &one << 1);
        assert_eq!(BoxedUint::from(4u8), &one << 2);
        assert_eq!(
            BoxedUint::from(0x80000000000000000u128),
            one.shl_vartime(67).unwrap()
        );
    }

    #[test]
    fn shl1_assign() {
        let mut n = BoxedUint::from(0x3c442b21f19185fe433f0a65af902b8fu128);
        let n_shl1 = BoxedUint::from(0x78885643e3230bfc867e14cb5f20571eu128);
        n.shl1_assign();
        assert_eq!(n, n_shl1);
    }

    #[test]
    fn shl_vartime() {
        let one = BoxedUint::one_with_precision(128);

        assert_eq!(BoxedUint::from(2u8), one.shl_vartime(1).unwrap());
        assert_eq!(BoxedUint::from(4u8), one.shl_vartime(2).unwrap());
        assert_eq!(
            BoxedUint::from(0x80000000000000000u128),
            one.shl_vartime(67).unwrap()
        );
    }
}
