//! [`BoxedUint`] bitwise right shift operations.

use crate::{BoxedUint, Limb};
use core::ops::{Shr, ShrAssign};
use subtle::{Choice, ConstantTimeLess};

impl BoxedUint {
    /// Computes `self << shift`.
    /// Returns zero if `shift >= Self::BITS`.
    pub fn shr(&self, shift: u32) -> Self {
        let overflow = !shift.ct_lt(&self.bits_precision());
        let shift = shift % self.bits_precision();
        let log2_bits = u32::BITS - self.bits_precision().leading_zeros();
        let mut result = self.clone();

        for i in 0..log2_bits {
            let bit = Choice::from(((shift >> i) & 1) as u8);
            result = Self::conditional_select(&result, &result.shr_vartime(1 << i), bit);
        }

        Self::conditional_select(
            &result,
            &Self::zero_with_precision(self.bits_precision()),
            overflow,
        )
    }

    /// Computes `self >> shift`.
    ///
    /// NOTE: this operation is variable time with respect to `shift` *ONLY*.
    ///
    /// When used with a fixed `shift`, this function is constant-time with respect to `self`.
    #[inline(always)]
    pub fn shr_vartime(&self, shift: u32) -> Self {
        let nlimbs = self.nlimbs();
        let full_shifts = (shift / Limb::BITS) as usize;
        let small_shift = shift & (Limb::BITS - 1);
        let mut limbs = vec![Limb::ZERO; nlimbs].into_boxed_slice();

        if shift > self.bits_precision() {
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
        Self::shr(&self, shift)
    }
}

impl Shr<u32> for &BoxedUint {
    type Output = BoxedUint;

    fn shr(self, shift: u32) -> BoxedUint {
        self.shr(shift)
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
        assert_eq!(BoxedUint::zero(), n.shr_vartime(68));
        assert_eq!(BoxedUint::one(), n.shr_vartime(67));
        assert_eq!(BoxedUint::from(2u8), n.shr_vartime(66));
        assert_eq!(BoxedUint::from(4u8), n.shr_vartime(65));
    }
}
