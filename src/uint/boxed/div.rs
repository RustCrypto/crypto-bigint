//! [`BoxedUint`] division operations.

use crate::{
    BoxedUint, CheckedDiv, ConstantTimeSelect, DivRemLimb, DivVartime, Limb, NonZero, Reciprocal,
    RemLimb, RemMixed, UintRef, Wrapping,
};
use core::ops::{Div, DivAssign, Rem, RemAssign};
use subtle::CtOption;

impl BoxedUint {
    /// Computes `self / rhs` using a pre-made reciprocal,
    /// returns the quotient (q) and remainder (r).
    pub fn div_rem_limb_with_reciprocal(&self, reciprocal: &Reciprocal) -> (Self, Limb) {
        let mut quo = self.clone();
        let rem = quo
            .as_mut_uint_ref()
            .div_rem_limb_with_reciprocal(reciprocal);
        (quo, rem)
    }

    /// Computes `self / rhs`, returns the quotient (q) and remainder (r).
    pub fn div_rem_limb(&self, rhs: NonZero<Limb>) -> (Self, Limb) {
        let mut quo = self.clone();
        let rem = quo.as_mut_uint_ref().div_rem_limb(rhs);
        (quo, rem)
    }

    /// Computes `self % rhs` using a pre-made reciprocal.
    #[inline(always)]
    pub fn rem_limb_with_reciprocal(&self, reciprocal: &Reciprocal) -> Limb {
        self.as_uint_ref()
            .rem_limb_with_reciprocal(reciprocal, Limb::ZERO)
    }

    /// Computes `self % rhs`.
    #[inline(always)]
    pub fn rem_limb(&self, rhs: NonZero<Limb>) -> Limb {
        self.as_uint_ref().rem_limb(rhs)
    }

    /// Computes self / rhs, returns the quotient, remainder.
    pub fn div_rem(&self, rhs: &NonZero<Self>) -> (Self, Self) {
        let (mut quo, mut rem) = (self.clone(), rhs.as_ref().clone());
        quo.as_mut_uint_ref().div_rem(rem.as_mut_uint_ref());
        (quo, rem)
    }

    /// Computes self % rhs, returns the remainder.
    pub fn rem(&self, rhs: &NonZero<Self>) -> Self {
        let xc = self.limbs.len();
        let yc = rhs.0.limbs.len();
        let (mut quo, mut rem) = (self.clone(), rhs.as_ref().clone());
        let x = quo.as_mut_uint_ref().split_at_mut(xc.saturating_sub(yc));
        UintRef::rem_wide(x, rem.as_mut_uint_ref());
        rem
    }

    /// Computes self / rhs, returns the quotient and remainder.
    ///
    /// Variable-time with respect to `rhs`
    pub fn div_rem_vartime(&self, rhs: &NonZero<Self>) -> (Self, Self) {
        let (mut quo, mut rem) = (self.clone(), rhs.as_ref().clone());
        quo.as_mut_uint_ref().div_rem_vartime(rem.as_mut_uint_ref());
        (quo, rem)
    }

    /// Computes self % rhs, returns the remainder.
    ///
    /// Variable-time with respect to `rhs`.
    pub fn rem_vartime(&self, rhs: &NonZero<Self>) -> Self {
        let xc = self.limbs.len();
        let yc = rhs.0.bits_vartime().div_ceil(Limb::BITS) as usize;

        match yc {
            0 => panic!("zero divisor"),
            1 => {
                // Perform limb division
                let rem_limb = self
                    .as_uint_ref()
                    .rem_limb(rhs.0.limbs[0].to_nz().expect("zero divisor"));
                let mut rem = Self::zero_with_precision(rhs.bits_precision());
                rem.limbs[0] = rem_limb;
                rem
            }
            _ if yc > xc => {
                let mut rem = Self::zero_with_precision(rhs.bits_precision());
                rem.limbs[..xc].copy_from_slice(&self.limbs);
                rem
            }
            _ => {
                let mut quo = self.clone();
                let mut rem = rhs.0.clone();
                let x = quo.as_mut_uint_ref().split_at_mut(xc - yc);
                UintRef::rem_wide_vartime(x, rem.as_mut_uint_ref());
                rem
            }
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
    /// This function exists, so that all operations are accounted for in the wrapping operations
    pub fn wrapping_div_vartime(&self, rhs: &NonZero<Self>) -> Self {
        self.div_rem_vartime(rhs).0
    }

    /// Perform checked division, returning a [`CtOption`] which `is_some`
    /// only if the rhs != 0
    pub fn checked_div(&self, rhs: &Self) -> CtOption<Self> {
        let mut quo = self.clone();
        let is_nz = rhs.is_nonzero();
        let mut rem = Self::one_with_precision(self.bits_precision());
        rem.ct_assign(rhs, is_nz);
        quo.as_mut_uint_ref().div_rem(rem.as_mut_uint_ref());
        CtOption::new(quo, is_nz)
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

impl DivVartime for BoxedUint {
    fn div_vartime(&self, rhs: &NonZero<BoxedUint>) -> Self {
        self.div_rem_vartime(rhs).0
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

impl DivRemLimb for BoxedUint {
    fn div_rem_limb_with_reciprocal(&self, reciprocal: &Reciprocal) -> (Self, Limb) {
        Self::div_rem_limb_with_reciprocal(self, reciprocal)
    }
}

impl RemLimb for BoxedUint {
    fn rem_limb_with_reciprocal(&self, reciprocal: &Reciprocal) -> Limb {
        Self::rem_limb_with_reciprocal(self, reciprocal)
    }
}

impl RemMixed<BoxedUint> for BoxedUint {
    fn rem_mixed(&self, reductor: &NonZero<BoxedUint>) -> BoxedUint {
        Self::div_rem_vartime(self, reductor).1
    }
}

#[cfg(test)]
mod tests {
    use crate::{DivVartime, Resize, Zero};

    use super::{BoxedUint, Limb, NonZero};

    #[test]
    fn rem() {
        let n = BoxedUint::from(0xFFEECCBBAA99887766u128);
        let p = NonZero::new(BoxedUint::from(997u128)).unwrap();
        assert_eq!(BoxedUint::from(648u128), n.rem(&p));
    }

    #[test]
    fn div_rem_larger_denominator() {
        // 1 = len(x) < len(y) and x < y
        let x = BoxedUint::from_be_hex("8000000000000000", 64).unwrap();
        let y = BoxedUint::from_be_hex("00000000000000010000000000000000", 128)
            .unwrap()
            .to_nz()
            .unwrap();
        let (quo, rem) = x.div_rem(&y);
        assert_eq!(quo, BoxedUint::zero_with_precision(64));
        assert_eq!(rem, x.resize_unchecked(128));

        // 1 = len(x) < len(y) and x > y
        let x = BoxedUint::from_be_hex("8000000000000000", 64).unwrap();
        let y = BoxedUint::from_be_hex("00000000000000000000000000001000", 128)
            .unwrap()
            .to_nz()
            .unwrap();
        let (quo, rem) = x.div_rem(&y);
        assert_eq!(quo, BoxedUint::from_be_hex("0008000000000000", 64).unwrap());
        assert_eq!(rem, BoxedUint::zero_with_precision(128));

        // 2 = len(x) < len(y) and x < y
        let x = BoxedUint::from_be_hex("80000000000000008000000000000000", 128).unwrap();
        let y = BoxedUint::from_be_hex(
            "0000000000000001000000000000000000000000000000010000000000000000",
            256,
        )
        .unwrap()
        .to_nz()
        .unwrap();
        let (quo, rem) = x.div_rem(&y);
        assert_eq!(quo, BoxedUint::zero_with_precision(128));
        assert_eq!(rem, x.resize_unchecked(256));

        // 2 = len(x) < len(y) and x > y
        let x = BoxedUint::from_be_hex("80000000000000008000000000000000", 128).unwrap();
        let y = BoxedUint::from_be_hex(
            "0000000000000000000000000000000000000000000000000000000000110000",
            256,
        )
        .unwrap()
        .to_nz()
        .unwrap();
        let (quo, rem) = x.div_rem(&y);
        assert_eq!(
            quo,
            BoxedUint::from_be_hex("000007878787878787878f0f0f0f0f0f", 128).unwrap()
        );
        assert_eq!(
            rem,
            BoxedUint::from_be_hex(
                "0000000000000000000000000000000000000000000000000000000000010000",
                256
            )
            .unwrap()
        );
    }

    #[test]
    fn rem_vartime() {
        let n = BoxedUint::from(0xFFEECCBBAA99887766u128);
        let p = NonZero::new(BoxedUint::from(997u128)).unwrap();
        assert_eq!(BoxedUint::from(648u128), n.rem_vartime(&p));
    }

    #[test]
    fn rem_limb() {
        let n = BoxedUint::from(0xFFEECCBBAA99887766u128);
        let pl = NonZero::new(Limb(997)).unwrap();
        let p = NonZero::new(BoxedUint::from(997u128)).unwrap();
        assert_eq!(n.rem(&p).limbs[0], n.rem_limb(pl));
    }

    #[test]
    fn div_vartime_through_trait() {
        struct A<T> {
            x: T,
            y: T,
        }
        impl<T: DivVartime + Clone + Zero> A<T> {
            fn divide_x_by_y(&self) -> T {
                let rhs = &NonZero::new(self.y.clone()).unwrap();
                self.x.div_vartime(rhs)
            }
        }

        let a = A {
            x: BoxedUint::from(1234567890u64),
            y: BoxedUint::from(456u64),
        };
        assert_eq!(a.divide_x_by_y(), BoxedUint::from(2707385u64));
    }
}
