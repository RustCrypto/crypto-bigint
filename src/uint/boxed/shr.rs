//! [`BoxedUint`] bitwise right shift operations.

use crate::{limb::HI_BIT, BoxedUint, Limb, Word};
use core::ops::{Shr, ShrAssign};
use subtle::{Choice, ConstantTimeLess};

impl BoxedUint {
    /// Computes `self >> 1` in constant-time, returning [`CtChoice::TRUE`] if the overflowing bit
    /// was set, and [`CtChoice::FALSE`] otherwise.
    pub(crate) fn shr_1(&self) -> (Self, Choice) {
        let nlimbs = self.nlimbs();
        let mut shifted_bits = vec![0; nlimbs];

        for i in 0..nlimbs {
            shifted_bits[i] = self.limbs[i].0 >> 1;
        }

        let mut carry_bits = vec![0; nlimbs];
        for i in 0..nlimbs {
            carry_bits[i] = self.limbs[i].0 << HI_BIT;
        }

        let mut limbs = vec![Limb(0); nlimbs];
        for i in 0..(nlimbs - 1) {
            limbs[i] = Limb(shifted_bits[i] | carry_bits[i + 1]);
        }
        limbs[nlimbs - 1] = Limb(shifted_bits[nlimbs - 1]);

        debug_assert!(carry_bits[nlimbs - 1] == 0 || carry_bits[nlimbs - 1] == (1 << HI_BIT));
        (limbs.into(), Choice::from((carry_bits[0] >> HI_BIT) as u8))
    }

    /// Computes `self >> shift`.
    ///
    /// NOTE: this operation is variable time with respect to `shift` *ONLY*.
    ///
    /// When used with a fixed `shift`, this function is constant-time with respect to `self`.
    #[inline(always)]
    pub fn shr_vartime(&self, shift: usize) -> Self {
        let nlimbs = self.nlimbs();
        let full_shifts = shift / Limb::BITS;
        let small_shift = shift & (Limb::BITS - 1);
        let mut limbs = vec![Limb::ZERO; nlimbs].into_boxed_slice();

        if shift > Limb::BITS * nlimbs {
            return Self { limbs };
        }

        let n = nlimbs - full_shifts;
        let mut i = 0;

        if small_shift == 0 {
            while i < n {
                limbs[i] = Limb(self.limbs[i + full_shifts].0);
                i += 1;
            }
        } else {
            while i < n {
                let mut lo = self.limbs[i + full_shifts].0 >> small_shift;

                if i < (nlimbs - 1) - full_shifts {
                    lo |= self.limbs[i + full_shifts + 1].0 << (Limb::BITS - small_shift);
                }

                limbs[i] = Limb(lo);
                i += 1;
            }
        }

        Self { limbs }
    }

    /// Computes `self << n`.
    /// Returns zero if `n >= Self::BITS`.
    pub fn shr(&self, shift: usize) -> Self {
        let overflow = !(shift as Word).ct_lt(&(self.bits_precision() as Word));
        let shift = shift % self.bits_precision();
        let log2_bits = (usize::BITS - self.bits_precision().leading_zeros()) as usize;
        let mut result = self.clone();

        for i in 0..log2_bits {
            let bit = Choice::from(((shift as Word >> i) & 1) as u8);
            result = Self::conditional_select(&result, &result.shr_vartime(1 << i), bit);
        }

        Self::conditional_select(
            &result,
            &Self::zero_with_precision(self.bits_precision()),
            overflow,
        )
    }
}

impl Shr<usize> for BoxedUint {
    type Output = BoxedUint;

    /// NOTE: this operation is variable time with respect to `rhs` *ONLY*.
    ///
    /// When used with a fixed `rhs`, this function is constant-time with respect
    /// to `self`.
    fn shr(self, rhs: usize) -> BoxedUint {
        Self::shr(&self, rhs)
    }
}

impl Shr<usize> for &BoxedUint {
    type Output = BoxedUint;

    /// NOTE: this operation is variable time with respect to `rhs` *ONLY*.
    ///
    /// When used with a fixed `rhs`, this function is constant-time with respect
    /// to `self`.
    fn shr(self, rhs: usize) -> BoxedUint {
        self.shr(rhs)
    }
}

impl ShrAssign<usize> for BoxedUint {
    fn shr_assign(&mut self, rhs: usize) {
        // TODO(tarcieri): in-place implementation that avoids clone
        *self = self.clone().shr(rhs);
    }
}

#[cfg(test)]
mod tests {
    use super::BoxedUint;

    #[test]
    fn shr_vartime() {
        let n = BoxedUint::from(0x80000000000000000u128);
        assert_eq!(BoxedUint::zero(), n.shr_vartime(68));
        assert_eq!(BoxedUint::one(), n.shr_vartime(67));
        assert_eq!(BoxedUint::from(2u8), n.shr_vartime(66));
        assert_eq!(BoxedUint::from(4u8), n.shr_vartime(65));
    }
}
