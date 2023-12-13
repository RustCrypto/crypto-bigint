//! Limb left bitshift

use crate::Limb;
use core::ops::{Shl, ShlAssign};

impl Limb {
    /// Computes `self << shift`.
    /// Panics if `shift` overflows `Limb::BITS`.
    #[inline(always)]
    pub const fn shl(self, shift: u32) -> Self {
        Limb(self.0 << shift)
    }

    /// Computes `self << 1` and return the result and the carry (0 or 1).
    #[inline(always)]
    pub(crate) const fn shl1(self) -> (Self, Self) {
        (Self(self.0 << 1), Self(self.0 >> Self::HI_BIT))
    }
}

impl Shl<u32> for Limb {
    type Output = Self;

    #[inline(always)]
    fn shl(self, shift: u32) -> Self::Output {
        self.shl(shift)
    }
}

impl ShlAssign<u32> for Limb {
    #[inline(always)]
    fn shl_assign(&mut self, shift: u32) {
        *self = self.shl(shift);
    }
}

#[cfg(test)]
mod tests {
    use crate::Limb;

    #[test]
    fn shl1() {
        assert_eq!(Limb(1) << 1, Limb(2));
    }

    #[test]
    fn shl2() {
        assert_eq!(Limb(1) << 2, Limb(4));
    }

    #[test]
    fn shl_assign1() {
        let mut l = Limb(1);
        l <<= 1;
        assert_eq!(l, Limb(2));
    }

    #[test]
    fn shl_assign2() {
        let mut l = Limb(1);
        l <<= 2;
        assert_eq!(l, Limb(4));
    }
}
