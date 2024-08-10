//! [`BoxedUint`] division operations.

use crate::{
    uint::{boxed, div_limb::div3by2},
    BoxedUint, CheckedDiv, ConstChoice, ConstantTimeSelect, DivRemLimb, Limb, NonZero, Reciprocal,
    RemLimb, Wrapping,
};
use core::ops::{Div, DivAssign, Rem, RemAssign};
use subtle::{Choice, ConstantTimeLess, CtOption};

impl BoxedUint {
    /// Computes `self / rhs` using a pre-made reciprocal,
    /// returns the quotient (q) and remainder (r).
    pub fn div_rem_limb_with_reciprocal(&self, reciprocal: &Reciprocal) -> (Self, Limb) {
        boxed::div_limb::div_rem_limb_with_reciprocal(self, reciprocal)
    }

    /// Computes `self / rhs`, returns the quotient (q) and remainder (r).
    pub fn div_rem_limb(&self, rhs: NonZero<Limb>) -> (Self, Limb) {
        boxed::div_limb::div_rem_limb_with_reciprocal(self, &Reciprocal::new(rhs))
    }

    /// Computes `self % rhs` using a pre-made reciprocal.
    #[inline(always)]
    pub fn rem_limb_with_reciprocal(&self, reciprocal: &Reciprocal) -> Limb {
        boxed::div_limb::rem_limb_with_reciprocal(self, reciprocal)
    }

    /// Computes `self % rhs`.
    #[inline(always)]
    pub fn rem_limb(&self, rhs: NonZero<Limb>) -> Limb {
        boxed::div_limb::rem_limb_with_reciprocal(self, &Reciprocal::new(rhs))
    }

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
        let yc = ((rhs.0.bits_vartime() + Limb::BITS - 1) / Limb::BITS) as usize;

        match yc {
            0 => panic!("zero divisor"),
            1 => {
                // Perform limb division
                let (quo, rem_limb) =
                    self.div_rem_limb(rhs.0.limbs[0].to_nz().expect("zero divisor"));
                let mut rem = Self::zero_with_precision(rhs.bits_precision());
                rem.limbs[0] = rem_limb;
                (quo, rem)
            }
            _ => {
                let mut quo = self.clone();
                let mut rem = rhs.0.clone();
                div_rem_vartime_in_place(&mut quo.limbs, &mut rem.limbs[..yc]);
                (quo, rem)
            }
        }
    }

    /// Computes self % rhs, returns the remainder.
    ///
    /// Variable-time with respect to `rhs`.
    pub fn rem_vartime(&self, rhs: &NonZero<Self>) -> Self {
        let yc = ((rhs.0.bits_vartime() + Limb::BITS - 1) / Limb::BITS) as usize;

        match yc {
            0 => panic!("zero divisor"),
            1 => {
                // Perform limb division
                let rem_limb = self.rem_limb(rhs.0.limbs[0].to_nz().expect("zero divisor"));
                let mut rem = Self::zero_with_precision(rhs.bits_precision());
                rem.limbs[0] = rem_limb;
                rem
            }
            _ if yc > self.limbs.len() => {
                let mut rem = Self::zero_with_precision(rhs.bits_precision());
                rem.limbs[..self.limbs.len()].copy_from_slice(&self.limbs);
                rem
            }
            _ => {
                let mut quo = self.clone();
                let mut rem = rhs.0.clone();
                div_rem_vartime_in_place(&mut quo.limbs, &mut rem.limbs[..yc]);
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

/// Computes `limbs << shift` inplace, where `0 <= shift < Limb::BITS`, returning the carry.
fn shl_limb_vartime(limbs: &mut [Limb], shift: u32) -> Limb {
    if shift == 0 {
        return Limb::ZERO;
    }

    let lshift = shift;
    let rshift = Limb::BITS - shift;
    let limbs_num = limbs.len();

    let carry = limbs[limbs_num - 1] >> rshift;
    for i in (1..limbs_num).rev() {
        limbs[i] = (limbs[i] << lshift) | (limbs[i - 1] >> rshift);
    }
    limbs[0] <<= lshift;

    carry
}

/// Computes `limbs >> shift` inplace, where `0 <= shift < Limb::BITS`.
fn shr_limb_vartime(limbs: &mut [Limb], shift: u32) {
    if shift == 0 {
        return;
    }

    let lshift = Limb::BITS - shift;
    let rshift = shift;

    let limbs_num = limbs.len();

    for i in 0..limbs_num - 1 {
        limbs[i] = (limbs[i] >> rshift) | (limbs[i + 1] << lshift);
    }
    limbs[limbs_num - 1] >>= rshift;
}

/// Computes `x` / `y`, returning the quotient in `x` and the remainder in `y`.
///
/// This function operates in variable-time. It will panic if the divisor is zero
/// or the leading word of the divisor is zero.
pub(crate) fn div_rem_vartime_in_place(x: &mut [Limb], y: &mut [Limb]) {
    let xc = x.len();
    let yc = y.len();
    assert!(
        yc > 0 && y[yc - 1].0 != 0,
        "divisor must have a non-zero leading word"
    );

    if xc == 0 {
        // If the quotient is empty, set the remainder to zero and return.
        y.fill(Limb::ZERO);
        return;
    } else if yc > xc {
        // Divisor is greater than dividend. Return zero and the dividend as the
        // quotient and remainder
        y[..xc].copy_from_slice(&x[..xc]);
        y[xc..].fill(Limb::ZERO);
        x.fill(Limb::ZERO);
        return;
    }

    let lshift = y[yc - 1].leading_zeros();

    // Shift divisor such that it has no leading zeros
    // This means that div2by1 requires no extra shifts, and ensures that the high word >= b/2
    shl_limb_vartime(y, lshift);

    // Shift the dividend to match
    let mut x_hi = shl_limb_vartime(x, lshift);

    let reciprocal = Reciprocal::new(y[yc - 1].to_nz().expect("zero divisor"));

    for xi in (yc - 1..xc).rev() {
        // Divide high dividend words by the high divisor word to estimate the quotient word
        let mut quo = div3by2(x_hi.0, x[xi].0, x[xi - 1].0, &reciprocal, y[yc - 2].0);

        // Subtract q*divisor from the dividend
        let borrow = {
            let mut carry = Limb::ZERO;
            let mut borrow = Limb::ZERO;
            let mut tmp;
            for i in 0..yc {
                (tmp, carry) = Limb::ZERO.mac(y[i], Limb(quo), carry);
                (x[xi + i + 1 - yc], borrow) = x[xi + i + 1 - yc].sbb(tmp, borrow);
            }
            (_, borrow) = x_hi.sbb(carry, borrow);
            borrow
        };

        // If the subtraction borrowed, then decrement q and add back the divisor
        // The probability of this being needed is very low, about 2/(Limb::MAX+1)
        quo = {
            let ct_borrow = ConstChoice::from_word_mask(borrow.0);
            let mut carry = Limb::ZERO;
            for i in 0..yc {
                (x[xi + i + 1 - yc], carry) =
                    x[xi + i + 1 - yc].adc(Limb::select(Limb::ZERO, y[i], ct_borrow), carry);
            }
            ct_borrow.select_word(quo, quo.saturating_sub(1))
        };

        // Store the quotient within dividend and set x_hi to the current highest word
        x_hi = x[xi];
        x[xi] = Limb(quo);
    }

    // Copy the remainder to divisor
    y[..yc - 1].copy_from_slice(&x[..yc - 1]);
    y[yc - 1] = x_hi;

    // Unshift the remainder from the earlier adjustment
    shr_limb_vartime(y, lshift);

    // Shift the quotient to the low limbs within dividend
    // let x_size = xc - yc + 1;
    x.copy_within(yc - 1..xc, 0);
    x[xc - yc + 1..].fill(Limb::ZERO);
}

#[cfg(test)]
mod tests {
    use super::{BoxedUint, Limb, NonZero};

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

    #[test]
    fn rem_limb() {
        let n = BoxedUint::from(0xFFEECCBBAA99887766u128);
        let pl = NonZero::new(Limb(997)).unwrap();
        let p = NonZero::new(BoxedUint::from(997u128)).unwrap();
        assert_eq!(n.rem(&p).limbs[0], n.rem_limb(pl));
    }
}
