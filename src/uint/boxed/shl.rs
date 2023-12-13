//! [`BoxedUint`] bitwise left shift operations.

use crate::{BoxedUint, Limb};
use core::ops::{Shl, ShlAssign};
use subtle::{Choice, ConstantTimeLess};

impl BoxedUint {
    /// Computes `self << shift`.
    /// Returns `None` if `shift >= self.bits_precision()`.
    pub fn shl(&self, shift: u32) -> (Self, Choice) {
        // `floor(log2(bits_precision - 1))` is the number of bits in the representation of `shift`
        // (which lies in range `0 <= shift < bits_precision`).
        let shift_bits = u32::BITS - (self.bits_precision() - 1).leading_zeros();
        let overflow = !shift.ct_lt(&self.bits_precision());
        let shift = shift % self.bits_precision();
        let mut result = self.clone();
        let mut temp = self.clone();

        for i in 0..shift_bits {
            let bit = Choice::from(((shift >> i) & 1) as u8);
            temp.set_to_zero();
            // Will not overflow by construction
            result
                .shl_vartime_into(&mut temp, 1 << i)
                .expect("shift within range");
            result.conditional_assign(&temp, bit);
        }

        result.conditional_set_to_zero(overflow);

        (result, overflow)
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
    pub(crate) fn shl1(&self) -> Self {
        let mut ret = self.clone();
        ret.shl1_assign();
        ret
    }

    /// Computes `self << 1` in-place in constant-time.
    pub(crate) fn shl1_assign(&mut self) {
        let mut carry = self.limbs[0].0 >> Limb::HI_BIT;
        self.limbs[0].shl_assign(1);
        for i in 1..self.limbs.len() {
            let new_carry = self.limbs[i].0 >> Limb::HI_BIT;
            self.limbs[i].shl_assign(1);
            self.limbs[i].0 |= carry;
            carry = new_carry
        }
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
    fn shl1_assign() {
        let mut n = BoxedUint::from(0x3c442b21f19185fe433f0a65af902b8fu128);
        let n_shl1 = BoxedUint::from(0x78885643e3230bfc867e14cb5f20571eu128);
        n.shl1_assign();
        assert_eq!(n, n_shl1);
    }

    #[test]
    fn shl() {
        let one = BoxedUint::one_with_precision(128);

        assert_eq!(BoxedUint::from(2u8), one.shl(1).0);
        assert_eq!(BoxedUint::from(4u8), one.shl(2).0);
        assert_eq!(
            BoxedUint::from(0x80000000000000000u128),
            one.shl_vartime(67).unwrap()
        );
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
