//! Limb right bitshift

use crate::Limb;
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
}

impl Shr<u32> for Limb {
    type Output = Self;

    #[inline(always)]
    fn shr(self, shift: u32) -> Self::Output {
        self.shr(shift)
    }
}

impl ShrAssign<u32> for Limb {
    #[inline(always)]
    fn shr_assign(&mut self, shift: u32) {
        *self = self.shr(shift);
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
