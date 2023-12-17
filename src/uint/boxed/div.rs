//! [`BoxedUint`] division operations.

use crate::{
    limb::div::div_wide,
    uint::{add::add2, cmp::cmp_slice, sub::sub2},
    BoxedUint, CheckedDiv, CheckedSub, Limb, NonZero, Word, Wrapping,
};
use core::{
    cmp::Ordering,
    ops::{Div, DivAssign, Rem, RemAssign},
};
use subtle::{Choice, ConstantTimeLess, CtOption};

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
    /// Panics if `self` has less precision than `rhs`.
    // TODO(tarcieri): handle different precisions without panicking
    pub fn rem_vartime(&self, rhs: &NonZero<Self>) -> Self {
        self.div_rem_vartime(rhs).1
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
        // normalize to avoid excess work
        let this = self.normalize_vartime();
        let rhs = rhs.normalize_vartime();

        // 0 / x = 0
        if bool::from(this.is_zero()) {
            return (Self::zero(), Self::zero());
        }

        // rhs is just a single word
        if rhs.as_words().len() == 1 {
            // division by 1
            if rhs.as_words()[0] == 1 {
                return (this.clone(), Self::zero());
            }

            let (div, rem) = this.div_rem_digit(rhs.as_words()[0]);
            return (div, rem.into());
        }

        // Required as the q_len calculation below can underflow:
        match this.cmp(&rhs) {
            Ordering::Less => return (Self::zero(), self.clone()),
            Ordering::Equal => return (Self::one(), Self::zero()),
            Ordering::Greater => {} // Do nothing
        }

        // This algorithm is from Knuth, TAOCP vol 2 section 4.3, algorithm D:
        //
        // First, normalize the arguments so the highest bit in the highest digit of the divisor is
        // set: the main loop uses the highest digit of the divisor for generating guesses, so we
        // want it to be the largest number we can efficiently divide by.
        let shift = rhs.as_words().last().unwrap().leading_zeros();
        std::dbg!(shift, this.as_words(), rhs.as_words());
        let mut a = this.shl_vartime(shift).unwrap().normalize_vartime();
        let b = rhs.shl_vartime(shift).unwrap().normalize_vartime();

        // The algorithm works by incrementally calculating "guesses", q0, for part of the
        // remainder. Once we have any number q0 such that q0 * b <= a, we can set
        //
        //     q += q0
        //     a -= q0 * b
        //
        // and then iterate until a < b. Then, (q, a) will be our desired quotient and remainder.
        //
        // q0, our guess, is calculated by dividing the last few digits of a by the last digit of b
        // - this should give us a guess that is "close" to the actual quotient, but is possibly
        // greater than the actual quotient. If q0 * b > a, we simply use iterated subtraction
        // until we have a guess such that q0 * b <= a.

        let bn = *b.as_words().last().unwrap();
        debug_assert!(
            a.as_words().len() >= b.as_words().len(),
            "{:?} - {:?} - {:?} - {:?}",
            a.as_words(),
            b.as_words(),
            this.as_words(),
            rhs.as_words(),
        );
        let q_len = (a.as_words().len() - b.as_words().len() + 1) as u32;
        let mut q = Self::zero_with_precision(q_len * Word::BITS);
        debug_assert_eq!(q.as_words().len(), q_len as _);

        for j in (0..q_len).rev() {
            // When calculating our next guess q0, we don't need to consider the digits below j
            // + b.data.len() - 1: we're guessing digit j of the quotient (i.e. q0 << j) from
            // digit bn of the divisor (i.e. bn << (b.data.len() - 1) - so the product of those
            // two numbers will be zero in all digits up to (j + b.data.len() - 1).
            let offset = (j as usize) + b.as_words().len() - 1;
            if offset >= a.as_words().len() {
                continue;
            }

            let a0 = Self::from_words(a.as_words()[offset..].iter().copied());

            // q0 << j * Word::BITS is our actual quotient estimate - we do the shifts
            // implicitly at the end, when adding and subtracting to a and q. Not only do we
            // save the cost of the shifts, the rest of the arithmetic gets to work with
            // smaller numbers.
            let (mut q0, _) = a0.div_rem_digit(bn);
            let mut prod = b.mul(&q0).normalize_vartime();

            std::dbg!(prod.as_words(), &a.as_words(), j);
            while cmp_slice(&prod.limbs, &a.as_limbs()[(j as usize)..]) == Ordering::Greater {
                let one = Self::one();
                q0 = q0.checked_sub(&one).unwrap();
                prod = prod.checked_sub(&b).unwrap();
            }

            add2(&mut q.as_limbs_mut()[(j as usize)..], q0.as_limbs());
            sub2(&mut a.as_limbs_mut()[(j as usize)..], prod.as_limbs());
            a = a.normalize_vartime();
        }

        debug_assert!(a < b);

        (q.normalize_vartime(), a >> shift)
    }

    /// Division by a single word.
    ///
    /// This function operates in variable-time.
    fn div_rem_digit(&self, b: Word) -> (Self, Word) {
        let mut out = self.clone();
        let mut rem = 0;

        for d in out.as_words_mut().iter_mut().rev() {
            let (q, r) = div_wide(rem, *d, b);
            *d = q;
            rem = r;
        }

        (out.normalize_vartime(), rem)
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
