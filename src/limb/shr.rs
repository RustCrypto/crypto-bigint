//! Limb right bitshift

use crate::{ConstChoice, Limb, WrappingShr};
use core::ops::{Shr, ShrAssign};

impl Limb {
    /// Computes `self >> shift`.
    /// Panics if `shift` overflows `Limb::BITS`.
    #[inline(always)]
    pub const fn shr(self, shift: u32) -> Self {
        Limb(self.0 >> shift)
    }

    /// Computes `self >> 1` and return the result and the carry (0 or `1 << HI_BIT`).
    #[inline(always)]
    pub(crate) const fn shr1(self) -> (Self, Self) {
        (Self(self.0 >> 1), Self(self.0 << Self::HI_BIT))
    }

    /// Computes `self >> shift` and returns the result as well as the carry: the `shift` _most_
    /// significant bits of the `carry` are equal to the `shift` _least_ significant bits of `self`.
    ///
    /// Panics if `shift` overflows `Limb::BITS`.
    #[inline(always)]
    pub const fn carrying_shr(self, shift: u32) -> (Self, Self) {
        // Note that we can compute carry = self << (Self::BITS - shift) whenever shift > 0.
        // However, we need to account for the case that shift = 0:
        // - the carry should be 0, and
        // - the value by which carry is left shifted should be made to be < Self::BITS.
        let shift_is_zero = ConstChoice::from_u32_eq(shift, 0);
        let carry = Self::select(self, Self::ZERO, shift_is_zero);
        let left_shift = shift_is_zero.select_u32(Self::BITS - shift, 0);

        (self.shr(shift), carry.shl(left_shift))
    }
}

macro_rules! impl_shr {
    ($($shift:ty),+) => {
        $(
            impl Shr<$shift> for Limb {
                type Output = Limb;

                #[inline]
                fn shr(self, shift: $shift) -> Limb {
                     Self::shr(self, u32::try_from(shift).expect("invalid shift"))
                }
            }

            impl Shr<$shift> for &Limb {
                type Output = Limb;

                #[inline]
                fn shr(self, shift: $shift) -> Limb {
                   *self >> shift
                }
            }

            impl ShrAssign<$shift> for Limb {
                #[inline]
                fn shr_assign(&mut self, shift: $shift) {
                    *self = *self >> shift;
                }
            }
        )+
    };
}

impl_shr!(i32, u32, usize);

impl WrappingShr for Limb {
    #[inline]
    fn wrapping_shr(&self, shift: u32) -> Limb {
        Self(self.0.wrapping_shr(shift))
    }
}

#[cfg(test)]
mod tests {
    use crate::Limb;

    #[test]
    fn shr1() {
        assert_eq!(Limb(2) >> 1, Limb(1));
    }

    #[test]
    fn shr2() {
        assert_eq!(Limb(16) >> 2, Limb(4));
    }

    #[test]
    fn shr_assign1() {
        let mut l = Limb::ONE;
        l >>= 1;
        assert_eq!(l, Limb::ZERO);
    }

    #[test]
    fn shr_assign2() {
        let mut l = Limb(32);
        l >>= 2;
        assert_eq!(l, Limb(8));
    }
}
