//! [`BoxedUint`] division operations.

use crate::{BoxedUint, CheckedDiv, Limb, NonZero, Wrapping};
use core::ops::{Div, DivAssign, Rem, RemAssign};
use subtle::{Choice, ConstantTimeEq, CtOption};

impl BoxedUint {
    /// Computes self / rhs, returns the quotient, remainder.
    ///
    /// Variable-time with respect to `rhs`
    pub fn div_rem_vartime(&self, rhs: &NonZero<Self>) -> (Self, Self) {
        self.div_rem_vartime_unchecked(rhs.as_ref())
    }

    /// Computes self % rhs, returns the remainder.
    ///
    /// Variable-time with respect to `rhs`.
    ///
    /// # Panics
    ///
    /// Panics if `self` and `rhs` have different precisions.
    // TODO(tarcieri): handle different precisions without panicking
    pub fn rem_vartime(&self, rhs: &NonZero<Self>) -> Self {
        debug_assert_eq!(self.bits_precision(), rhs.bits_precision());
        let mb = rhs.bits();
        let mut bd = self.bits_precision() - mb;
        let mut rem = self.clone();
        let mut c = rhs.shl_vartime(bd);

        loop {
            let (r, borrow) = rem.sbb(&c, Limb::ZERO);
            rem = Self::conditional_select(&r, &rem, !borrow.ct_eq(&Limb::ZERO));
            if bd == 0 {
                break rem;
            }
            bd -= 1;
            c = c.shr_vartime(1);
        }
    }

    /// Wrapped division is just normal division i.e. `self` / `rhs`
    /// There’s no way wrapping could ever happen.
    ///
    /// This function exists, so that all operations are accounted for in the wrapping operations.
    ///
    /// Panics if `rhs == 0`.
    pub fn wrapping_div(&self, rhs: &NonZero<Self>) -> Self {
        self.div_rem_vartime(rhs).0
    }

    /// Perform checked division, returning a [`CtOption`] which `is_some`
    /// only if the rhs != 0
    pub fn checked_div(&self, rhs: &Self) -> CtOption<Self> {
        CtOption::new(self.div_rem_vartime_unchecked(rhs).0, rhs.is_zero())
    }

    /// Compute divison and remainder without checking `rhs` is zero.
    fn div_rem_vartime_unchecked(&self, rhs: &Self) -> (Self, Self) {
        debug_assert_eq!(self.bits_precision(), rhs.bits_precision());
        let mb = rhs.bits();
        let mut bd = self.bits_precision() - mb;
        let mut remainder = self.clone();
        let mut quotient = Self::zero_with_precision(self.bits_precision());
        let mut c = rhs.shl(bd);

        loop {
            let (mut r, borrow) = remainder.sbb(&c, Limb::ZERO);
            let borrow = Choice::from(borrow.0 as u8 & 1);
            remainder = Self::conditional_select(&r, &remainder, borrow);
            r = &quotient | Self::one();
            quotient = Self::conditional_select(&r, &quotient, borrow);
            if bd == 0 {
                break;
            }
            bd -= 1;
            c = c.shr(1);
            quotient = quotient.shl(1);
        }

        (quotient, remainder)
    }
}

impl CheckedDiv<BoxedUint> for BoxedUint {
    type Output = Self;

    fn checked_div(&self, rhs: BoxedUint) -> CtOption<Self> {
        self.checked_div(&rhs)
    }
}

impl CheckedDiv<&BoxedUint> for BoxedUint {
    type Output = Self;

    fn checked_div(&self, rhs: &BoxedUint) -> CtOption<Self> {
        self.checked_div(rhs)
    }
}

impl Div<&NonZero<BoxedUint>> for &BoxedUint {
    type Output = BoxedUint;

    fn div(self, rhs: &NonZero<BoxedUint>) -> Self::Output {
        self.wrapping_div(rhs)
    }
}

impl Div<&NonZero<BoxedUint>> for BoxedUint {
    type Output = BoxedUint;

    fn div(self, rhs: &NonZero<BoxedUint>) -> Self::Output {
        self.wrapping_div(rhs)
    }
}

impl Div<NonZero<BoxedUint>> for &BoxedUint {
    type Output = BoxedUint;

    fn div(self, rhs: NonZero<BoxedUint>) -> Self::Output {
        self.wrapping_div(&rhs)
    }
}

impl Div<NonZero<BoxedUint>> for BoxedUint {
    type Output = BoxedUint;

    fn div(self, rhs: NonZero<BoxedUint>) -> Self::Output {
        self.div_rem_vartime(&rhs).0
    }
}

impl DivAssign<&NonZero<BoxedUint>> for BoxedUint {
    fn div_assign(&mut self, rhs: &NonZero<BoxedUint>) {
        *self = self.wrapping_div(rhs);
    }
}

impl DivAssign<NonZero<BoxedUint>> for BoxedUint {
    fn div_assign(&mut self, rhs: NonZero<BoxedUint>) {
        *self = self.wrapping_div(&rhs);
    }
}

impl Div<NonZero<BoxedUint>> for Wrapping<BoxedUint> {
    type Output = Wrapping<BoxedUint>;

    fn div(self, rhs: NonZero<BoxedUint>) -> Self::Output {
        Wrapping(self.0 / rhs)
    }
}

impl Div<NonZero<BoxedUint>> for &Wrapping<BoxedUint> {
    type Output = Wrapping<BoxedUint>;

    fn div(self, rhs: NonZero<BoxedUint>) -> Self::Output {
        Wrapping(self.0.wrapping_div(&rhs))
    }
}

impl Div<&NonZero<BoxedUint>> for &Wrapping<BoxedUint> {
    type Output = Wrapping<BoxedUint>;

    fn div(self, rhs: &NonZero<BoxedUint>) -> Self::Output {
        Wrapping(self.0.wrapping_div(rhs))
    }
}

impl Div<&NonZero<BoxedUint>> for Wrapping<BoxedUint> {
    type Output = Wrapping<BoxedUint>;

    fn div(self, rhs: &NonZero<BoxedUint>) -> Self::Output {
        Wrapping(self.0.wrapping_div(rhs))
    }
}

impl DivAssign<&NonZero<BoxedUint>> for Wrapping<BoxedUint> {
    fn div_assign(&mut self, rhs: &NonZero<BoxedUint>) {
        *self = Wrapping(&self.0 / rhs);
    }
}

impl DivAssign<NonZero<BoxedUint>> for Wrapping<BoxedUint> {
    fn div_assign(&mut self, rhs: NonZero<BoxedUint>) {
        *self /= &rhs;
    }
}

impl Rem<&NonZero<BoxedUint>> for &BoxedUint {
    type Output = BoxedUint;

    #[inline]
    fn rem(self, rhs: &NonZero<BoxedUint>) -> Self::Output {
        self.rem_vartime(rhs)
    }
}

impl Rem<&NonZero<BoxedUint>> for BoxedUint {
    type Output = BoxedUint;

    #[inline]
    fn rem(self, rhs: &NonZero<BoxedUint>) -> Self::Output {
        self.rem_vartime(rhs)
    }
}

impl Rem<NonZero<BoxedUint>> for &BoxedUint {
    type Output = BoxedUint;

    #[inline]
    fn rem(self, rhs: NonZero<BoxedUint>) -> Self::Output {
        self.rem_vartime(&rhs)
    }
}

impl Rem<NonZero<BoxedUint>> for BoxedUint {
    type Output = BoxedUint;

    #[inline]
    fn rem(self, rhs: NonZero<BoxedUint>) -> Self::Output {
        self.rem_vartime(&rhs)
    }
}

impl RemAssign<&NonZero<BoxedUint>> for BoxedUint {
    fn rem_assign(&mut self, rhs: &NonZero<BoxedUint>) {
        *self = self.rem_vartime(rhs)
    }
}

impl RemAssign<NonZero<BoxedUint>> for BoxedUint {
    fn rem_assign(&mut self, rhs: NonZero<BoxedUint>) {
        *self = self.rem_vartime(&rhs)
    }
}

#[cfg(test)]
mod tests {
    use super::{BoxedUint, NonZero};

    #[test]
    fn rem_vartime() {
        let n = BoxedUint::from(0xFFEECCBBAA99887766u128);
        let p = NonZero::new(BoxedUint::from(997u128)).unwrap();
        assert_eq!(BoxedUint::from(648u128), n.rem_vartime(&p));
    }
}
