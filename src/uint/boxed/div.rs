//! [`BoxedUint`] division operations.

use crate::{BoxedUint, CheckedDiv, ConstantTimeSelect, Limb, NonZero, Wrapping};
use core::ops::{Div, DivAssign, Rem, RemAssign};
use subtle::{Choice, ConstantTimeEq, ConstantTimeLess, CtOption};

impl BoxedUint {
    /// Computes self / rhs, returns the quotient, remainder.
    pub fn div_rem(&self, rhs: &NonZero<Self>) -> (Self, Self) {
        // Since `rhs` is nonzero, this should always hold.
        self.div_rem_unchecked(rhs.as_ref())
    }

    /// Computes self % rhs, returns the remainder.
    pub fn rem(&self, rhs: &NonZero<Self>) -> Self {
        self.div_rem(rhs).1
    }

    /// Computes self / rhs, returns the quotient, remainder.
    ///
    /// Variable-time with respect to `rhs`
    pub fn div_rem_vartime(&self, rhs: &NonZero<Self>) -> (Self, Self) {
        // Since `rhs` is nonzero, this should always hold.
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
        // Will not overflow since `bd < bits_precision`
        let mut c = rhs.shl_vartime(bd).expect("shift within range");

        loop {
            let (r, borrow) = rem.sbb(&c, Limb::ZERO);
            rem = Self::ct_select(&r, &rem, !borrow.ct_eq(&Limb::ZERO));
            if bd == 0 {
                break rem;
            }
            bd -= 1;
            c.shr1_assign();
        }
    }

    /// Wrapped division is just normal division i.e. `self` / `rhs`
    /// There’s no way wrapping could ever happen.
    ///
    /// This function exists, so that all operations are accounted for in the wrapping operations.
    ///
    /// Panics if `rhs == 0`.
    pub fn wrapping_div(&self, rhs: &NonZero<Self>) -> Self {
        self.div_rem(rhs).0
    }

    /// Wrapped division is just normal division i.e. `self` / `rhs`
    ///
    /// There’s no way wrapping could ever happen.
    /// This function exists, so that all operations are accounted for in the wrapping operations.
    pub fn wrapping_div_vartime(&self, rhs: &NonZero<Self>) -> Self {
        let (q, _) = self.div_rem_vartime(rhs);
        q
    }

    /// Perform checked division, returning a [`CtOption`] which `is_some`
    /// only if the rhs != 0
    pub fn checked_div(&self, rhs: &Self) -> CtOption<Self> {
        let q = self.div_rem_unchecked(rhs).0;
        CtOption::new(q, !rhs.is_zero())
    }

    /// Computes `self` / `rhs`, returns the quotient (q), remainder (r) without checking if `rhs`
    /// is zero.
    ///
    /// This function is constant-time with respect to both `self` and `rhs`.
    fn div_rem_unchecked(&self, rhs: &Self) -> (Self, Self) {
        debug_assert_eq!(self.bits_precision(), rhs.bits_precision());
        let mb = rhs.bits();
        let bits_precision = self.bits_precision();
        let mut rem = self.clone();
        let mut quo = Self::zero_with_precision(bits_precision);
        let (mut c, _overflow) = rhs.overflowing_shl(bits_precision - mb);
        let mut i = bits_precision;
        let mut done = Choice::from(0u8);

        loop {
            let (mut r, borrow) = rem.sbb(&c, Limb::ZERO);
            rem.ct_assign(&r, !(Choice::from((borrow.0 & 1) as u8) | done));
            r = quo.bitor(&Self::one());
            quo.ct_assign(&r, !(Choice::from((borrow.0 & 1) as u8) | done));
            if i == 0 {
                break;
            }
            i -= 1;
            // when `i < mb`, the computation is actually done, so we ensure `quo` and `rem`
            // aren't modified further (but do the remaining iterations anyway to be constant-time)
            done = i.ct_lt(&mb);
            c.shr1_assign();
            quo.ct_assign(&quo.shl1(), !done);
        }

        (quo, rem)
    }

    /// Computes `self` / `rhs`, returns the quotient (q), remainder (r) without checking if `rhs`
    /// is zero.
    ///
    /// This function operates in variable-time.
    fn div_rem_vartime_unchecked(&self, rhs: &Self) -> (Self, Self) {
        debug_assert_eq!(self.bits_precision(), rhs.bits_precision());
        let mb = rhs.bits_vartime();
        let mut bd = self.bits_precision() - mb;
        let mut remainder = self.clone();
        let mut quotient = Self::zero_with_precision(self.bits_precision());
        // Will not overflow since `bd < bits_precision`
        let mut c = rhs.shl_vartime(bd).expect("shift within range");

        loop {
            let (mut r, borrow) = remainder.sbb(&c, Limb::ZERO);
            let borrow = Choice::from(borrow.0 as u8 & 1);
            remainder = Self::ct_select(&r, &remainder, borrow);
            r = &quotient | Self::one();
            quotient = Self::ct_select(&r, &quotient, borrow);
            if bd == 0 {
                break;
            }
            bd -= 1;
            c.shr1_assign();
            quotient.shl1_assign();
        }

        (quotient, remainder)
    }
}

impl CheckedDiv for BoxedUint {
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
        self.div_rem(&rhs).0
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
        self.rem(rhs)
    }
}

impl Rem<&NonZero<BoxedUint>> for BoxedUint {
    type Output = BoxedUint;

    #[inline]
    fn rem(self, rhs: &NonZero<BoxedUint>) -> Self::Output {
        Self::rem(&self, rhs)
    }
}

impl Rem<NonZero<BoxedUint>> for &BoxedUint {
    type Output = BoxedUint;

    #[inline]
    fn rem(self, rhs: NonZero<BoxedUint>) -> Self::Output {
        self.rem(&rhs)
    }
}

impl Rem<NonZero<BoxedUint>> for BoxedUint {
    type Output = BoxedUint;

    #[inline]
    fn rem(self, rhs: NonZero<BoxedUint>) -> Self::Output {
        self.rem(&rhs)
    }
}

impl RemAssign<&NonZero<BoxedUint>> for BoxedUint {
    fn rem_assign(&mut self, rhs: &NonZero<BoxedUint>) {
        *self = Self::rem(self, rhs)
    }
}

impl RemAssign<NonZero<BoxedUint>> for BoxedUint {
    fn rem_assign(&mut self, rhs: NonZero<BoxedUint>) {
        *self = Self::rem(self, &rhs)
    }
}

#[cfg(test)]
mod tests {
    use super::{BoxedUint, NonZero};

    #[test]
    fn rem() {
        let n = BoxedUint::from(0xFFEECCBBAA99887766u128);
        let p = NonZero::new(BoxedUint::from(997u128)).unwrap();
        assert_eq!(BoxedUint::from(648u128), n.rem(&p));
    }

    #[test]
    fn rem_vartime() {
        let n = BoxedUint::from(0xFFEECCBBAA99887766u128);
        let p = NonZero::new(BoxedUint::from(997u128)).unwrap();
        assert_eq!(BoxedUint::from(648u128), n.rem_vartime(&p));
    }
}
