//! [`BoxedUint`] bitwise left shift operations.

use crate::{BoxedUint, Limb, Word};
use core::ops::{Shl, ShlAssign};
use subtle::{Choice, ConstantTimeLess};

impl BoxedUint {
    /// Computes `self << shift` where `0 <= shift < Limb::BITS`,
    /// returning the result and the carry.
    #[inline(always)]
    pub(crate) fn shl_limb(&self, n: usize) -> (Self, Limb) {
        let nlimbs = self.nlimbs();
        let mut limbs = vec![Limb::ZERO; nlimbs].into_boxed_slice();

        let nz = Limb(n as Word).ct_is_nonzero();
        let lshift = n as Word;
        let rshift = Limb::ct_select(Limb::ZERO, Limb((Limb::BITS - n) as Word), nz).0;
        let carry = Limb::ct_select(
            Limb::ZERO,
            Limb(self.limbs[nlimbs - 1].0.wrapping_shr(Word::BITS - n as u32)),
            nz,
        );

        let mut i = nlimbs - 1;
        while i > 0 {
            let mut limb = self.limbs[i].0 << lshift;
            let hi = self.limbs[i - 1].0 >> rshift;
            limb |= nz.if_true(hi);
            limbs[i] = Limb(limb);
            i -= 1
        }
        limbs[0] = Limb(self.limbs[0].0 << lshift);

        (Self { limbs }, carry)
    }

    /// Computes `self << shift`.
    ///
    /// NOTE: this operation is variable time with respect to `shift` *ONLY*.
    ///
    /// When used with a fixed `shift`, this function is constant-time with respect to `self`.
    #[inline(always)]
    pub fn shl_vartime(&self, shift: usize) -> Self {
        let nlimbs = self.nlimbs();
        let mut limbs = vec![Limb::ZERO; nlimbs].into_boxed_slice();

        if shift >= Limb::BITS * nlimbs {
            return Self { limbs };
        }

        let shift_num = shift / Limb::BITS;
        let rem = shift % Limb::BITS;

        let mut i = nlimbs;
        while i > shift_num {
            i -= 1;
            limbs[i] = self.limbs[i - shift_num];
        }

        let (new_lower, _carry) = (Self { limbs }).shl_limb(rem);
        new_lower
    }

    /// Computes `self << n`.
    /// Returns zero if `n >= Self::BITS`.
    pub fn shl(&self, shift: usize) -> Self {
        let overflow = !(shift as Word).ct_lt(&(self.bits_precision() as Word));
        let shift = shift % self.bits_precision();
        let log2_bits = (usize::BITS - self.bits_precision().leading_zeros()) as usize;
        let mut result = self.clone();

        for i in 0..log2_bits {
            let bit = Choice::from(((shift as Word >> i) & 1) as u8);
            result = Self::conditional_select(&result, &result.shl_vartime(1 << i), bit);
        }

        Self::conditional_select(
            &result,
            &Self::zero_with_precision(self.bits_precision()),
            overflow,
        )
    }
}

impl Shl<usize> for BoxedUint {
    type Output = BoxedUint;

    /// NOTE: this operation is variable time with respect to `rhs` *ONLY*.
    ///
    /// When used with a fixed `rhs`, this function is constant-time with respect
    /// to `self`.
    fn shl(self, rhs: usize) -> BoxedUint {
        Self::shl(&self, rhs)
    }
}

impl Shl<usize> for &BoxedUint {
    type Output = BoxedUint;

    /// NOTE: this operation is variable time with respect to `rhs` *ONLY*.
    ///
    /// When used with a fixed `rhs`, this function is constant-time with respect
    /// to `self`.
    fn shl(self, rhs: usize) -> BoxedUint {
        self.shl(rhs)
    }
}

impl ShlAssign<usize> for BoxedUint {
    /// NOTE: this operation is variable time with respect to `rhs` *ONLY*.
    ///
    /// When used with a fixed `rhs`, this function is constant-time with respect
    /// to `self`.
    fn shl_assign(&mut self, rhs: usize) {
        // TODO(tarcieri): in-place implementation that avoids clone
        *self = self.clone().shl(rhs)
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
