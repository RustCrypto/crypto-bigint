//! [`BoxedUint`] bitwise left shift operations.

use crate::{BoxedUint, Limb};
use core::ops::{Shl, ShlAssign};
use subtle::{Choice, ConstantTimeLess};

impl BoxedUint {
    /// Computes `self << shift`.
    /// Returns `None` if `shift >= Self::BITS`.
    pub fn shl(&self, shift: u32) -> (Self, Choice) {
        // `floor(log2(bits_precision - 1))` is the number of bits in the representation of `shift`
        // (which lies in range `0 <= shift < bits_precision`).
        let shift_bits = u32::BITS - (self.bits_precision() - 1).leading_zeros();
        let overflow = !shift.ct_lt(&self.bits_precision());
        let shift = shift % self.bits_precision();
        let mut result = self.clone();

        for i in 0..shift_bits {
            let bit = Choice::from(((shift >> i) & 1) as u8);
            result = Self::conditional_select(
                &result,
                // Will not overflow by construction
                &result.shl_vartime(1 << i).expect("shift within range"),
                bit,
            );
        }

        (
            Self::conditional_select(
                &result,
                &Self::zero_with_precision(self.bits_precision()),
                overflow,
            ),
            overflow,
        )
    }

    /// Computes `self << shift`.
    /// Returns `None` if `shift >= Self::BITS`.
    ///
    /// NOTE: this operation is variable time with respect to `shift` *ONLY*.
    ///
    /// When used with a fixed `shift`, this function is constant-time with respect to `self`.
    #[inline(always)]
    pub fn shl_vartime(&self, shift: u32) -> Option<Self> {
        if shift >= self.bits_precision() {
            return None;
        }

        let nlimbs = self.nlimbs();
        let mut limbs = vec![Limb::ZERO; nlimbs].into_boxed_slice();

        let shift_num = (shift / Limb::BITS) as usize;
        let rem = shift % Limb::BITS;

        let mut i = nlimbs;
        while i > shift_num {
            i -= 1;
            limbs[i] = self.limbs[i - shift_num];
        }

        if rem == 0 {
            return Some(Self { limbs });
        }

        let mut carry = Limb::ZERO;

        while i < nlimbs {
            let shifted = limbs[i].shl(rem);
            let new_carry = limbs[i].shr(Limb::BITS - rem);
            limbs[i] = shifted.bitor(carry);
            carry = new_carry;
            i += 1;
        }

        Some(Self { limbs })
    }

    /// Computes `self >> 1` in constant-time.
    pub(crate) fn shl1(&self) -> Self {
        // TODO(tarcieri): optimized implementation
        self.shl_vartime(1).expect("shift within range")
    }

    /// Computes `self >> 1` in-place in constant-time.
    pub(crate) fn shl1_assign(&mut self) {
        // TODO(tarcieri): optimized implementation
        *self = self.shl1();
    }
}

impl Shl<u32> for BoxedUint {
    type Output = BoxedUint;

    fn shl(self, shift: u32) -> BoxedUint {
        <&BoxedUint as Shl<u32>>::shl(&self, shift)
    }
}

impl Shl<u32> for &BoxedUint {
    type Output = BoxedUint;

    fn shl(self, shift: u32) -> BoxedUint {
        let (result, overflow) = self.shl(shift);
        assert!(!bool::from(overflow), "attempt to shift left with overflow");
        result
    }
}

impl ShlAssign<u32> for BoxedUint {
    fn shl_assign(&mut self, shift: u32) {
        // TODO(tarcieri): in-place implementation that avoids clone
        *self = self.clone().shl(shift)
    }
}

#[cfg(test)]
mod tests {
    use super::BoxedUint;

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
