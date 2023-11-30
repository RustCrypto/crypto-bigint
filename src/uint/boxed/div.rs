//! [`BoxedUint`] division operations.

use crate::{BoxedUint, Limb, NonZero};
use core::ops::{Rem, RemAssign};
use subtle::ConstantTimeEq;

impl BoxedUint {
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
