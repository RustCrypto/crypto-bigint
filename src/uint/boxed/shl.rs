//! [`BoxedUint`] bitwise left shift operations.

use crate::{BoxedUint, CtChoice, Limb, Word};
use core::ops::{Shl, ShlAssign};
use subtle::{Choice, ConstantTimeLess};

impl BoxedUint {
    /// Computes `self << shift`.
    /// Returns zero if `shift >= Self::BITS`.
    pub fn shl(&self, shift: u32) -> Self {
        let overflow = !shift.ct_lt(&self.bits_precision());
        let shift = shift % self.bits_precision();
        let log2_bits = u32::BITS - self.bits_precision().leading_zeros();
        let mut result = self.clone();

        for i in 0..log2_bits {
            let bit = Choice::from(((shift >> i) & 1) as u8);
            result = Self::conditional_select(&result, &result.shl_vartime(1 << i), bit);
        }

        Self::conditional_select(
            &result,
            &Self::zero_with_precision(self.bits_precision()),
            overflow,
        )
    }

    /// Computes `self << shift`.
    ///
    /// NOTE: this operation is variable time with respect to `shift` *ONLY*.
    ///
    /// When used with a fixed `shift`, this function is constant-time with respect to `self`.
    #[inline(always)]
    pub fn shl_vartime(&self, shift: u32) -> Self {
        let nlimbs = self.nlimbs();
        let mut limbs = vec![Limb::ZERO; nlimbs].into_boxed_slice();

        if shift >= self.bits_precision() {
            return Self { limbs };
        }

        let shift_num = (shift / Limb::BITS) as usize;
        let rem = shift % Limb::BITS;

        let mut i = nlimbs;
        while i > shift_num {
            i -= 1;
            limbs[i] = self.limbs[i - shift_num];
        }

        let (new_lower, _carry) = (Self { limbs }).shl_limb(rem);
        new_lower
    }

    /// Computes `self << shift` where `0 <= shift < Limb::BITS`,
    /// returning the result and the carry.
    #[inline(always)]
    pub(crate) fn shl_limb(&self, shift: u32) -> (Self, Limb) {
        let nlimbs = self.nlimbs();
        let mut limbs = vec![Limb::ZERO; nlimbs].into_boxed_slice();

        let nz = CtChoice::from_u32_nonzero(shift);
        let lshift = shift;
        let rshift = nz.if_true_u32(Limb::BITS - shift);
        let carry = nz.if_true_word(self.limbs[nlimbs - 1].0.wrapping_shr(Word::BITS - shift));

        let mut i = nlimbs - 1;
        while i > 0 {
            let mut limb = self.limbs[i].0 << lshift;
            let hi = self.limbs[i - 1].0 >> rshift;
            limb |= nz.if_true_word(hi);
            limbs[i] = Limb(limb);
            i -= 1
        }
        limbs[0] = Limb(self.limbs[0].0 << lshift);

        (Self { limbs }, Limb(carry))
    }
}

impl Shl<u32> for BoxedUint {
    type Output = BoxedUint;

    fn shl(self, shift: u32) -> BoxedUint {
        Self::shl(&self, shift)
    }
}

impl Shl<u32> for &BoxedUint {
    type Output = BoxedUint;

    fn shl(self, shift: u32) -> BoxedUint {
        self.shl(shift)
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

        assert_eq!(BoxedUint::from(2u8), one.shl_vartime(1));
        assert_eq!(BoxedUint::from(4u8), one.shl_vartime(2));
        assert_eq!(
            BoxedUint::from(0x80000000000000000u128),
            one.shl_vartime(67)
        );
    }
}
