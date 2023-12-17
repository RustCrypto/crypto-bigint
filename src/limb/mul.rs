//! Limb multiplication

use crate::{
    primitives::{mac, mul_wide},
    Checked, CheckedMul, Limb, Wrapping, Zero,
};
use core::ops::{Mul, MulAssign};
use num_traits::WrappingMul;
use subtle::CtOption;

impl Limb {
    /// Computes `self + (b * c) + carry`, returning the result along with the new carry.
    #[inline(always)]
    pub const fn mac(self, b: Limb, c: Limb, carry: Limb) -> (Limb, Limb) {
        let (res, carry) = mac(self.0, b.0, c.0, carry.0);
        (Limb(res), Limb(carry))
    }

    /// Perform saturating multiplication.
    #[inline(always)]
    pub const fn saturating_mul(&self, rhs: Self) -> Self {
        Limb(self.0.saturating_mul(rhs.0))
    }

    /// Perform wrapping multiplication, discarding overflow.
    #[inline(always)]
    pub const fn wrapping_mul(&self, rhs: Self) -> Self {
        Limb(self.0.wrapping_mul(rhs.0))
    }

    /// Compute "wide" multiplication, with a product twice the size of the input.
    pub(crate) const fn mul_wide(&self, rhs: Self) -> (Self, Self) {
        let (lo, hi) = mul_wide(self.0, rhs.0);
        (Limb(lo), Limb(hi))
    }
}

impl CheckedMul for Limb {
    #[inline]
    fn checked_mul(&self, rhs: &Self) -> CtOption<Self> {
        let (lo, hi) = self.mul_wide(*rhs);
        CtOption::new(lo, hi.is_zero())
    }
}

impl Mul<Limb> for Limb {
    type Output = Limb;

    #[inline]
    fn mul(self, rhs: Limb) -> Self {
        self.checked_mul(&rhs)
            .expect("attempted to multiply with overflow")
    }
}

impl Mul<&Limb> for Limb {
    type Output = Limb;

    #[inline]
    fn mul(self, rhs: &Limb) -> Self {
        self * *rhs
    }
}

impl Mul<Limb> for &Limb {
    type Output = Limb;

    #[inline]
    fn mul(self, rhs: Limb) -> Self::Output {
        *self * rhs
    }
}

impl Mul<&Limb> for &Limb {
    type Output = Limb;

    #[inline]
    fn mul(self, rhs: &Limb) -> Self::Output {
        *self * *rhs
    }
}

impl MulAssign for Wrapping<Limb> {
    #[inline]
    fn mul_assign(&mut self, other: Self) {
        *self = *self * other;
    }
}

impl MulAssign<&Wrapping<Limb>> for Wrapping<Limb> {
    #[inline]
    fn mul_assign(&mut self, other: &Self) {
        *self = *self * other;
    }
}

impl MulAssign for Checked<Limb> {
    #[inline]
    fn mul_assign(&mut self, other: Self) {
        *self = *self * other;
    }
}

impl MulAssign<&Checked<Limb>> for Checked<Limb> {
    #[inline]
    fn mul_assign(&mut self, other: &Self) {
        *self = *self * other;
    }
}

impl WrappingMul for Limb {
    #[inline]
    fn wrapping_mul(&self, v: &Self) -> Self {
        self.wrapping_mul(*v)
    }
}

#[cfg(test)]
mod tests {
    use super::{CheckedMul, Limb};

    #[test]
    #[cfg(target_pointer_width = "32")]
    fn checked_mul_ok() {
        let n = Limb::from_u16(0xffff);
        assert_eq!(n.checked_mul(&n).unwrap(), Limb::from_u32(0xfffe_0001));
    }

    #[test]
    #[cfg(target_pointer_width = "64")]
    fn checked_mul_ok() {
        let n = Limb::from_u32(0xffff_ffff);
        assert_eq!(
            n.checked_mul(&n).unwrap(),
            Limb::from_u64(0xffff_fffe_0000_0001)
        );
    }

    #[test]
    fn checked_mul_overflow() {
        let n = Limb::MAX;
        assert!(bool::from(n.checked_mul(&n).is_none()));
    }
}
