//! [`BoxedUint`] bitwise right shift operations.

use crate::{BoxedUint, Limb};
use core::ops::{Shr, ShrAssign};
use subtle::{Choice, ConstantTimeLess};

impl BoxedUint {
    /// Computes `self >> shift`.
    /// Returns `None` if `shift >= Self::BITS`.
    pub fn shr(&self, shift: u32) -> (Self, Choice) {
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
                &result.shr_vartime(1 << i).expect("shift within range"),
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

    /// Computes `self >> shift`.
    /// Returns `None` if `shift >= Self::BITS`.
    ///
    /// NOTE: this operation is variable time with respect to `shift` *ONLY*.
    ///
    /// When used with a fixed `shift`, this function is constant-time with respect to `self`.
    #[inline(always)]
    pub fn shr_vartime(&self, shift: u32) -> Option<Self> {
        if shift >= self.bits_precision() {
            return None;
        }

        let nlimbs = self.nlimbs();
        let mut limbs = vec![Limb::ZERO; nlimbs].into_boxed_slice();

        let shift_num = (shift / Limb::BITS) as usize;
        let rem = shift % Limb::BITS;

        let mut i = 0;
        while i < nlimbs - shift_num {
            limbs[i] = self.limbs[i + shift_num];
            i += 1;
        }

        if rem == 0 {
            return Some(Self { limbs });
        }

        let mut carry = Limb::ZERO;

        while i > 0 {
            i -= 1;
            let shifted = limbs[i].shr(rem);
            let new_carry = limbs[i].shl(Limb::BITS - rem);
            limbs[i] = shifted.bitor(carry);
            carry = new_carry;
        }

        Some(Self { limbs })
    }

    /// Computes `self >> 1` in constant-time, returning a true [`Choice`] if the overflowing bit
    /// was set, and a false [`Choice::FALSE`] otherwise.
    pub(crate) fn shr1_with_overflow(&self) -> (Self, Choice) {
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

impl Shr<u32> for BoxedUint {
    type Output = BoxedUint;

    fn shr(self, shift: u32) -> BoxedUint {
        <&BoxedUint as Shr<u32>>::shr(&self, shift)
    }
}

impl Shr<u32> for &BoxedUint {
    type Output = BoxedUint;

    fn shr(self, shift: u32) -> BoxedUint {
        let (result, overflow) = self.shr(shift);
        assert!(
            !bool::from(overflow),
            "attempt to shift right with overflow"
        );
        result
    }
}

impl ShrAssign<u32> for BoxedUint {
    fn shr_assign(&mut self, shift: u32) {
        // TODO(tarcieri): in-place implementation that avoids clone
        *self = self.clone().shr(shift);
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
    fn shr_vartime() {
        let n = BoxedUint::from(0x80000000000000000u128);
        assert_eq!(BoxedUint::zero(), n.shr_vartime(68).unwrap());
        assert_eq!(BoxedUint::one(), n.shr_vartime(67).unwrap());
        assert_eq!(BoxedUint::from(2u8), n.shr_vartime(66).unwrap());
        assert_eq!(BoxedUint::from(4u8), n.shr_vartime(65).unwrap());
    }
}
