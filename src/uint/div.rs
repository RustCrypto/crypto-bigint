//! [`Uint`] division operations.

use super::div_limb::{
    div3by2, div_rem_limb_with_reciprocal, rem_limb_with_reciprocal, rem_limb_with_reciprocal_wide,
    Reciprocal,
};
use crate::{CheckedDiv, ConstChoice, DivRemLimb, Limb, NonZero, RemLimb, Uint, Word, Wrapping};
use core::ops::{Div, DivAssign, Rem, RemAssign};
use subtle::CtOption;

impl<const LIMBS: usize> Uint<LIMBS> {
    /// Computes `self / rhs` using a pre-made reciprocal,
    /// returns the quotient (q) and remainder (r).
    #[inline(always)]
    pub const fn div_rem_limb_with_reciprocal(&self, reciprocal: &Reciprocal) -> (Self, Limb) {
        div_rem_limb_with_reciprocal(self, reciprocal)
    }

    /// Computes `self / rhs`, returns the quotient (q) and remainder (r).
    #[inline(always)]
    pub const fn div_rem_limb(&self, rhs: NonZero<Limb>) -> (Self, Limb) {
        div_rem_limb_with_reciprocal(self, &Reciprocal::new(rhs))
    }

    /// Computes `self % rhs` using a pre-made reciprocal.
    #[inline(always)]
    pub const fn rem_limb_with_reciprocal(&self, reciprocal: &Reciprocal) -> Limb {
        rem_limb_with_reciprocal(self, reciprocal)
    }

    /// Computes `self % rhs`.
    #[inline(always)]
    pub const fn rem_limb(&self, rhs: NonZero<Limb>) -> Limb {
        rem_limb_with_reciprocal(self, &Reciprocal::new(rhs))
    }

    /// Computes `self` / `rhs`, returns the quotient (q) and the remainder (r)
    ///
    /// This function is constant-time with respect to both `self` and `rhs`.
    #[allow(trivial_numeric_casts)]
    pub const fn div_rem(&self, rhs: &NonZero<Self>) -> (Self, Self) {
        let mb = rhs.0.bits();
        let mut rem = *self;
        let mut quo = Self::ZERO;
        // If there is overflow, it means `mb == 0`, so `rhs == 0`.
        let mut c = rhs.0.wrapping_shl(Self::BITS - mb);

        let mut i = Self::BITS;
        let mut done = ConstChoice::FALSE;
        loop {
            let (r, borrow) = rem.sbb(&c, Limb::ZERO);
            let choice = ConstChoice::from_word_mask(borrow.0).or(done);
            rem = Self::select(&r, &rem, choice);
            quo = Self::select(&quo.bitor(&Self::ONE), &quo, choice);
            if i == 0 {
                break;
            }
            i -= 1;
            // when `i < mb`, the computation is actually done, so we ensure `quo` and `rem`
            // aren't modified further (but do the remaining iterations anyway to be constant-time)
            done = ConstChoice::from_word_lt(i as Word, mb as Word);
            c = c.shr1();
            quo = Self::select(&quo.shl1(), &quo, done);
        }

        (quo, rem)
    }

    /// Computes `self` / `rhs`, returns the quotient (q) and the remainder (r)
    ///
    /// This is variable only with respect to `rhs`.
    ///
    /// When used with a fixed `rhs`, this function is constant-time with respect
    /// to `self`.
    pub const fn div_rem_vartime<const RHS_LIMBS: usize>(
        &self,
        rhs: &NonZero<Uint<RHS_LIMBS>>,
    ) -> (Self, Uint<RHS_LIMBS>) {
        // Based on Section 4.3.1, of The Art of Computer Programming, Volume 2, by Donald E. Knuth.
        // Further explanation at https://janmr.com/blog/2014/04/basic-multiple-precision-long-division/

        let dbits = rhs.0.bits_vartime();
        let yc = ((dbits + Limb::BITS - 1) / Limb::BITS) as usize;

        // Short circuit for small or extra large divisors
        match yc {
            1 => {
                // If the divisor is a single limb, use limb division
                let (q, r) = div_rem_limb_with_reciprocal(
                    self,
                    &Reciprocal::new(rhs.0.limbs[0].to_nz().expect("zero divisor")),
                );
                return (q, Uint::from_word(r.0));
            }
            yc if yc > LIMBS => {
                // Divisor is greater than dividend. Return zero and the dividend as the
                // quotient and remainder
                return (Uint::ZERO, self.resize());
            }
            _ => {}
        };

        let lshift = (Limb::BITS - (dbits % Limb::BITS)) % Limb::BITS;
        let rshift = if lshift == 0 { 0 } else { Limb::BITS - lshift };
        let mut x = self.to_limbs();
        let mut x_hi = Limb::ZERO;
        let mut xi = LIMBS - 1;
        let mut y = rhs.0.to_limbs();
        let mut i;
        let mut carry;

        if lshift != 0 {
            // Shift divisor such that it has no leading zeros
            // This means that div2by1 requires no extra shifts, and ensures that the high word >= b/2
            i = 0;
            carry = Limb::ZERO;
            while i < yc {
                (y[i], carry) = (Limb((y[i].0 << lshift) | carry.0), Limb(y[i].0 >> rshift));
                i += 1;
            }

            // Shift the dividend to match
            i = 0;
            carry = Limb::ZERO;
            while i < LIMBS {
                (x[i], carry) = (Limb((x[i].0 << lshift) | carry.0), Limb(x[i].0 >> rshift));
                i += 1;
            }
            x_hi = carry;
        }

        let reciprocal = Reciprocal::new(y[yc - 1].to_nz().expect("zero divisor"));

        loop {
            // Divide high dividend words by the high divisor word to estimate the quotient word
            let (mut quo, _) = div3by2(x_hi.0, x[xi].0, x[xi - 1].0, &reciprocal, y[yc - 2].0);

            // Subtract q*divisor from the dividend
            carry = Limb::ZERO;
            let mut borrow = Limb::ZERO;
            let mut tmp;
            i = 0;
            while i < yc {
                (tmp, carry) = Limb::ZERO.mac(y[i], Limb(quo), carry);
                (x[xi + i + 1 - yc], borrow) = x[xi + i + 1 - yc].sbb(tmp, borrow);
                i += 1;
            }
            (_, borrow) = x_hi.sbb(carry, borrow);

            // If the subtraction borrowed, then decrement q and add back the divisor
            // The probability of this being needed is very low, about 2/(Limb::MAX+1)
            let ct_borrow = ConstChoice::from_word_mask(borrow.0);
            carry = Limb::ZERO;
            i = 0;
            while i < yc {
                (x[xi + i + 1 - yc], carry) =
                    x[xi + i + 1 - yc].adc(Limb::select(Limb::ZERO, y[i], ct_borrow), carry);
                i += 1;
            }
            quo = ct_borrow.select_word(quo, quo.saturating_sub(1));

            // Store the quotient within dividend and set x_hi to the current highest word
            x_hi = x[xi];
            x[xi] = Limb(quo);

            if xi == yc - 1 {
                break;
            }
            xi -= 1;
        }

        // Copy the remainder to divisor
        i = 0;
        while i < yc - 1 {
            y[i] = x[i];
            i += 1;
        }
        y[yc - 1] = x_hi;

        // Unshift the remainder from the earlier adjustment
        if lshift != 0 {
            i = yc;
            carry = Limb::ZERO;
            while i > 0 {
                i -= 1;
                (y[i], carry) = (Limb((y[i].0 >> lshift) | carry.0), Limb(y[i].0 << rshift));
            }
        }

        // Shift the quotient to the low limbs within dividend
        i = 0;
        while i < LIMBS {
            if i <= (LIMBS - yc) {
                x[i] = x[i + yc - 1];
            } else {
                x[i] = Limb::ZERO;
            }
            i += 1;
        }

        (Uint::new(x), Uint::new(y))
    }

    /// Computes `self` % `rhs`, returns the remainder.
    pub const fn rem(&self, rhs: &NonZero<Self>) -> Self {
        self.div_rem(rhs).1
    }

    /// Computes `self` % `rhs`, returns the remainder in variable-time with respect to `rhs`.
    ///
    /// When used with a fixed `rhs`, this function is constant-time with respect
    /// to `self`.
    pub const fn rem_vartime(&self, rhs: &NonZero<Self>) -> Self {
        self.div_rem_vartime(rhs).1
    }

    /// Computes `self` % `rhs`, returns the remainder.
    ///
    /// This is variable only with respect to `rhs`.
    ///
    /// When used with a fixed `rhs`, this function is constant-time with respect
    /// to `self`.
    pub const fn rem_wide_vartime(lower_upper: (Self, Self), rhs: &NonZero<Self>) -> Self {
        let dbits = rhs.0.bits_vartime();
        let yc = ((dbits + Limb::BITS - 1) / Limb::BITS) as usize;

        // If the divisor is a single limb, use limb division
        if yc == 1 {
            let r = rem_limb_with_reciprocal_wide(
                (&lower_upper.0, &lower_upper.1),
                &Reciprocal::new(rhs.0.limbs[0].to_nz().expect("zero divisor")),
            );
            return Uint::from_word(r.0);
        }

        let lshift = (Limb::BITS - (dbits % Limb::BITS)) % Limb::BITS;
        let rshift = if lshift == 0 { 0 } else { Limb::BITS - lshift };
        let mut x = lower_upper.1.to_limbs(); // high limbs
        let mut x_hi = Limb::ZERO;
        let mut xi = LIMBS - 1;
        let mut y = rhs.0.to_limbs();
        let mut extra_limbs = LIMBS;
        let mut i;
        let mut carry;

        if lshift != 0 {
            // Shift divisor such that it has no leading zeros
            // This ensures that the high word >= b/2, and means that div2by1 requires no extra shifts
            i = 0;
            carry = Limb::ZERO;
            while i < yc {
                (y[i], carry) = (Limb((y[i].0 << lshift) | carry.0), Limb(y[i].0 >> rshift));
                i += 1;
            }

            // Shift the dividend to match
            i = 0;
            carry = Limb(lower_upper.0.limbs[LIMBS - 1].0 >> rshift);
            while i < LIMBS {
                (x[i], carry) = (Limb((x[i].0 << lshift) | carry.0), Limb(x[i].0 >> rshift));
                i += 1;
            }
            x_hi = carry;
        }

        let reciprocal = Reciprocal::new(y[yc - 1].to_nz().expect("zero divisor"));

        loop {
            // Divide high dividend words by the high divisor word to estimate the quotient word
            let (quo, _) = div3by2(x_hi.0, x[xi].0, x[xi - 1].0, &reciprocal, y[yc - 2].0);

            // Subtract q*divisor from the dividend
            carry = Limb::ZERO;
            let mut borrow = Limb::ZERO;
            let mut tmp;
            i = 0;
            while i < yc {
                (tmp, carry) = Limb::ZERO.mac(y[i], Limb(quo), carry);
                (x[xi + i + 1 - yc], borrow) = x[xi + i + 1 - yc].sbb(tmp, borrow);
                i += 1;
            }
            (_, borrow) = x_hi.sbb(carry, borrow);

            // If the subtraction borrowed, then add back the divisor
            // The probability of this being needed is very low, about 2/(Limb::MAX+1)
            let ct_borrow = ConstChoice::from_word_mask(borrow.0);
            carry = Limb::ZERO;
            i = 0;
            while i < yc {
                (x[xi + i + 1 - yc], carry) =
                    x[xi + i + 1 - yc].adc(Limb::select(Limb::ZERO, y[i], ct_borrow), carry);
                i += 1;
            }

            // Set x_hi to the current highest word
            x_hi = x[xi];

            // If we have lower limbs remaining, shift the divisor words one word left
            if extra_limbs > 0 {
                extra_limbs -= 1;
                i = LIMBS - 1;
                while i > 0 {
                    x[i] = x[i - 1];
                    i -= 1;
                }
                x[0] = lower_upper.0.limbs[extra_limbs];
                if lshift != 0 {
                    x[0].0 <<= lshift;
                    if extra_limbs > 0 {
                        x[0].0 |= lower_upper.0.limbs[extra_limbs - 1].0 >> rshift;
                    }
                }
            } else {
                if xi == yc - 1 {
                    break;
                }
                xi -= 1;
            }
        }

        // Unshift the remainder from the earlier adjustment
        if lshift != 0 {
            i = yc;
            carry = Limb::ZERO;
            while i > 0 {
                i -= 1;
                (x[i], carry) = (Limb((x[i].0 >> lshift) | carry.0), Limb(x[i].0 << rshift));
            }
        }
        // Clear upper limbs
        i = LIMBS - 1;
        while i >= yc {
            x[i] = Limb::ZERO;
            i -= 1;
        }

        Uint::new(x)
    }

    /// Computes `self` % 2^k. Faster than reduce since its a power of 2.
    /// Limited to 2^16-1 since Uint doesn't support higher.
    ///
    /// ### Usage:
    /// ```
    /// use crypto_bigint::{U448, Limb};
    ///
    /// let a = U448::from(10_u64);
    /// let k = 3; // 2^3 = 8
    /// let remainder = a.rem2k_vartime(k);
    ///
    /// // As 10 % 8 = 2
    /// assert_eq!(remainder, U448::from(2_u64));
    /// ```
    pub const fn rem2k_vartime(&self, k: u32) -> Self {
        let highest = (LIMBS - 1) as u32;
        let index = k / Limb::BITS;
        let le = ConstChoice::from_u32_le(index, highest);
        let limb_num = le.select_u32(highest, index) as usize;

        let base = k % Limb::BITS;
        let mask = (1 << base) - 1;
        let mut out = *self;

        let outmask = Limb(out.limbs[limb_num].0 & mask);

        out.limbs[limb_num] = Limb::select(out.limbs[limb_num], outmask, le);

        // TODO: this is not constant-time.
        let mut i = limb_num + 1;
        while i < LIMBS {
            out.limbs[i] = Limb::ZERO;
            i += 1;
        }

        out
    }

    /// Wrapped division is just normal division i.e. `self` / `rhs`
    ///
    /// There’s no way wrapping could ever happen.
    /// This function exists, so that all operations are accounted for in the wrapping operations.
    pub const fn wrapping_div(&self, rhs: &NonZero<Self>) -> Self {
        self.div_rem(rhs).0
    }

    /// Wrapped division is just normal division i.e. `self` / `rhs`
    ///
    /// There’s no way wrapping could ever happen.
    /// This function exists, so that all operations are accounted for in the wrapping operations.
    pub const fn wrapping_div_vartime<const RHS: usize>(&self, rhs: &NonZero<Uint<RHS>>) -> Self {
        self.div_rem_vartime(rhs).0
    }

    /// Perform checked division, returning a [`CtOption`] which `is_some`
    /// only if the rhs != 0
    ///
    /// ### Usage:
    /// ```
    /// use crypto_bigint::{U448, NonZero, subtle::{CtOption, Choice}};
    ///
    /// let a = U448::from(8_u64);
    /// let result = NonZero::new(U448::from(4_u64))
    ///     .map(|b| a.div_rem(&b))
    ///     .expect("Division by zero");
    ///
    /// assert_eq!(result.0, U448::from(2_u64));
    ///
    /// // Check division by zero
    /// let zero = U448::from(0_u64);
    /// assert!(bool::from(a.checked_div(&zero).is_none()), "Should be None for division by zero");
    /// ```
    pub fn checked_div(&self, rhs: &Self) -> CtOption<Self> {
        NonZero::new(*rhs).map(|rhs| {
            let (q, _r) = self.div_rem(&rhs);
            q
        })
    }

    /// This function exists, so that all operations are accounted for in the wrapping operations.
    /// Panics if `rhs == 0`.
    ///
    /// ### Usage:
    /// ```
    /// use crypto_bigint::U448;
    ///
    /// let a = U448::from(10_u64);
    /// let b = U448::from(3_u64);
    /// let remainder = a.wrapping_rem_vartime(&b);
    ///
    /// assert_eq!(remainder, U448::from(1_u64));
    /// ```
    pub const fn wrapping_rem_vartime(&self, rhs: &Self) -> Self {
        let nz_rhs = rhs.to_nz().expect("non-zero divisor");
        self.rem_vartime(&nz_rhs)
    }

    /// Perform checked reduction, returning a [`CtOption`] which `is_some`
    /// only if the rhs != 0
    ///
    /// ### Usage:
    /// ```
    /// use crypto_bigint::{U448, NonZero, subtle::{Choice,CtOption}};
    ///
    /// let a = U448::from(10_u64);
    /// let remainder_option = NonZero::new(U448::from(3_u64))
    ///     .map(|b| a.rem(&b));
    ///
    /// assert!(bool::from(remainder_option.is_some()));
    ///
    /// // Check reduction by zero
    /// let zero = U448::from(0_u64);
    ///
    /// assert!(bool::from(a.checked_rem(&zero).is_none()), "Should be None for reduction by zero");
    /// ```
    pub fn checked_rem(&self, rhs: &Self) -> CtOption<Self> {
        NonZero::new(*rhs).map(|rhs| self.rem(&rhs))
    }
}

//
// Division by a single limb
//

impl<const LIMBS: usize> Div<&NonZero<Limb>> for &Uint<LIMBS> {
    type Output = Uint<LIMBS>;

    fn div(self, rhs: &NonZero<Limb>) -> Self::Output {
        *self / *rhs
    }
}

impl<const LIMBS: usize> Div<&NonZero<Limb>> for Uint<LIMBS> {
    type Output = Uint<LIMBS>;

    fn div(self, rhs: &NonZero<Limb>) -> Self::Output {
        self / *rhs
    }
}

impl<const LIMBS: usize> Div<NonZero<Limb>> for &Uint<LIMBS> {
    type Output = Uint<LIMBS>;

    fn div(self, rhs: NonZero<Limb>) -> Self::Output {
        *self / rhs
    }
}

impl<const LIMBS: usize> Div<NonZero<Limb>> for Uint<LIMBS> {
    type Output = Uint<LIMBS>;

    fn div(self, rhs: NonZero<Limb>) -> Self::Output {
        let (q, _) = self.div_rem_limb(rhs);
        q
    }
}

impl<const LIMBS: usize> DivAssign<&NonZero<Limb>> for Uint<LIMBS> {
    fn div_assign(&mut self, rhs: &NonZero<Limb>) {
        *self /= *rhs;
    }
}

impl<const LIMBS: usize> DivAssign<NonZero<Limb>> for Uint<LIMBS> {
    fn div_assign(&mut self, rhs: NonZero<Limb>) {
        *self = *self / rhs;
    }
}

impl<const LIMBS: usize> Div<NonZero<Limb>> for Wrapping<Uint<LIMBS>> {
    type Output = Wrapping<Uint<LIMBS>>;

    fn div(self, rhs: NonZero<Limb>) -> Self::Output {
        Wrapping(self.0 / rhs)
    }
}

impl<const LIMBS: usize> Div<NonZero<Limb>> for &Wrapping<Uint<LIMBS>> {
    type Output = Wrapping<Uint<LIMBS>>;

    fn div(self, rhs: NonZero<Limb>) -> Self::Output {
        *self / rhs
    }
}

impl<const LIMBS: usize> Div<&NonZero<Limb>> for &Wrapping<Uint<LIMBS>> {
    type Output = Wrapping<Uint<LIMBS>>;

    fn div(self, rhs: &NonZero<Limb>) -> Self::Output {
        *self / *rhs
    }
}

impl<const LIMBS: usize> Div<&NonZero<Limb>> for Wrapping<Uint<LIMBS>> {
    type Output = Wrapping<Uint<LIMBS>>;

    fn div(self, rhs: &NonZero<Limb>) -> Self::Output {
        self / *rhs
    }
}

impl<const LIMBS: usize> DivAssign<&NonZero<Limb>> for Wrapping<Uint<LIMBS>> {
    fn div_assign(&mut self, rhs: &NonZero<Limb>) {
        *self = Wrapping(self.0 / rhs)
    }
}

impl<const LIMBS: usize> DivAssign<NonZero<Limb>> for Wrapping<Uint<LIMBS>> {
    fn div_assign(&mut self, rhs: NonZero<Limb>) {
        *self /= &rhs;
    }
}

impl<const LIMBS: usize> Rem<&NonZero<Limb>> for &Uint<LIMBS> {
    type Output = Limb;

    fn rem(self, rhs: &NonZero<Limb>) -> Self::Output {
        *self % *rhs
    }
}

impl<const LIMBS: usize> Rem<&NonZero<Limb>> for Uint<LIMBS> {
    type Output = Limb;

    fn rem(self, rhs: &NonZero<Limb>) -> Self::Output {
        self % *rhs
    }
}

impl<const LIMBS: usize> Rem<NonZero<Limb>> for &Uint<LIMBS> {
    type Output = Limb;

    fn rem(self, rhs: NonZero<Limb>) -> Self::Output {
        *self % rhs
    }
}

impl<const LIMBS: usize> Rem<NonZero<Limb>> for Uint<LIMBS> {
    type Output = Limb;

    fn rem(self, rhs: NonZero<Limb>) -> Self::Output {
        let (_, r) = self.div_rem_limb(rhs);
        r
    }
}

impl<const LIMBS: usize> RemAssign<&NonZero<Limb>> for Uint<LIMBS> {
    fn rem_assign(&mut self, rhs: &NonZero<Limb>) {
        *self = (*self % rhs).into();
    }
}

impl<const LIMBS: usize> RemAssign<NonZero<Limb>> for Uint<LIMBS> {
    fn rem_assign(&mut self, rhs: NonZero<Limb>) {
        *self %= &rhs;
    }
}

impl<const LIMBS: usize> Rem<NonZero<Limb>> for Wrapping<Uint<LIMBS>> {
    type Output = Wrapping<Limb>;

    fn rem(self, rhs: NonZero<Limb>) -> Self::Output {
        Wrapping(self.0 % rhs)
    }
}

impl<const LIMBS: usize> Rem<NonZero<Limb>> for &Wrapping<Uint<LIMBS>> {
    type Output = Wrapping<Limb>;

    fn rem(self, rhs: NonZero<Limb>) -> Self::Output {
        *self % rhs
    }
}

impl<const LIMBS: usize> Rem<&NonZero<Limb>> for &Wrapping<Uint<LIMBS>> {
    type Output = Wrapping<Limb>;

    fn rem(self, rhs: &NonZero<Limb>) -> Self::Output {
        *self % *rhs
    }
}

impl<const LIMBS: usize> Rem<&NonZero<Limb>> for Wrapping<Uint<LIMBS>> {
    type Output = Wrapping<Limb>;

    fn rem(self, rhs: &NonZero<Limb>) -> Self::Output {
        self % *rhs
    }
}

impl<const LIMBS: usize> RemAssign<NonZero<Limb>> for Wrapping<Uint<LIMBS>> {
    fn rem_assign(&mut self, rhs: NonZero<Limb>) {
        *self %= &rhs;
    }
}

impl<const LIMBS: usize> RemAssign<&NonZero<Limb>> for Wrapping<Uint<LIMBS>> {
    fn rem_assign(&mut self, rhs: &NonZero<Limb>) {
        *self = Wrapping((self.0 % rhs).into())
    }
}

//
// Division by an Uint
//

impl<const LIMBS: usize> CheckedDiv for Uint<LIMBS> {
    fn checked_div(&self, rhs: &Uint<LIMBS>) -> CtOption<Self> {
        self.checked_div(rhs)
    }
}

impl<const LIMBS: usize> Div<&NonZero<Uint<LIMBS>>> for &Uint<LIMBS> {
    type Output = Uint<LIMBS>;

    fn div(self, rhs: &NonZero<Uint<LIMBS>>) -> Self::Output {
        *self / *rhs
    }
}

impl<const LIMBS: usize> Div<&NonZero<Uint<LIMBS>>> for Uint<LIMBS> {
    type Output = Uint<LIMBS>;

    fn div(self, rhs: &NonZero<Uint<LIMBS>>) -> Self::Output {
        self / *rhs
    }
}

impl<const LIMBS: usize> Div<NonZero<Uint<LIMBS>>> for &Uint<LIMBS> {
    type Output = Uint<LIMBS>;

    fn div(self, rhs: NonZero<Uint<LIMBS>>) -> Self::Output {
        *self / rhs
    }
}

impl<const LIMBS: usize> Div<NonZero<Uint<LIMBS>>> for Uint<LIMBS> {
    type Output = Uint<LIMBS>;

    fn div(self, rhs: NonZero<Uint<LIMBS>>) -> Self::Output {
        let (q, _) = self.div_rem(&rhs);
        q
    }
}

impl<const LIMBS: usize> DivAssign<&NonZero<Uint<LIMBS>>> for Uint<LIMBS> {
    fn div_assign(&mut self, rhs: &NonZero<Uint<LIMBS>>) {
        *self /= *rhs
    }
}

impl<const LIMBS: usize> DivAssign<NonZero<Uint<LIMBS>>> for Uint<LIMBS> {
    fn div_assign(&mut self, rhs: NonZero<Uint<LIMBS>>) {
        *self = *self / rhs;
    }
}

impl<const LIMBS: usize> Div<NonZero<Uint<LIMBS>>> for Wrapping<Uint<LIMBS>> {
    type Output = Wrapping<Uint<LIMBS>>;

    fn div(self, rhs: NonZero<Uint<LIMBS>>) -> Self::Output {
        Wrapping(self.0 / rhs)
    }
}

impl<const LIMBS: usize> Div<NonZero<Uint<LIMBS>>> for &Wrapping<Uint<LIMBS>> {
    type Output = Wrapping<Uint<LIMBS>>;

    fn div(self, rhs: NonZero<Uint<LIMBS>>) -> Self::Output {
        *self / rhs
    }
}

impl<const LIMBS: usize> Div<&NonZero<Uint<LIMBS>>> for &Wrapping<Uint<LIMBS>> {
    type Output = Wrapping<Uint<LIMBS>>;

    fn div(self, rhs: &NonZero<Uint<LIMBS>>) -> Self::Output {
        *self / *rhs
    }
}

impl<const LIMBS: usize> Div<&NonZero<Uint<LIMBS>>> for Wrapping<Uint<LIMBS>> {
    type Output = Wrapping<Uint<LIMBS>>;

    fn div(self, rhs: &NonZero<Uint<LIMBS>>) -> Self::Output {
        self / *rhs
    }
}

impl<const LIMBS: usize> DivAssign<&NonZero<Uint<LIMBS>>> for Wrapping<Uint<LIMBS>> {
    fn div_assign(&mut self, rhs: &NonZero<Uint<LIMBS>>) {
        *self = Wrapping(self.0 / rhs);
    }
}

impl<const LIMBS: usize> DivAssign<NonZero<Uint<LIMBS>>> for Wrapping<Uint<LIMBS>> {
    fn div_assign(&mut self, rhs: NonZero<Uint<LIMBS>>) {
        *self /= &rhs;
    }
}

impl<const LIMBS: usize> Rem<&NonZero<Uint<LIMBS>>> for &Uint<LIMBS> {
    type Output = Uint<LIMBS>;

    fn rem(self, rhs: &NonZero<Uint<LIMBS>>) -> Self::Output {
        *self % *rhs
    }
}

impl<const LIMBS: usize> Rem<&NonZero<Uint<LIMBS>>> for Uint<LIMBS> {
    type Output = Uint<LIMBS>;

    fn rem(self, rhs: &NonZero<Uint<LIMBS>>) -> Self::Output {
        self % *rhs
    }
}

impl<const LIMBS: usize> Rem<NonZero<Uint<LIMBS>>> for &Uint<LIMBS> {
    type Output = Uint<LIMBS>;

    fn rem(self, rhs: NonZero<Uint<LIMBS>>) -> Self::Output {
        *self % rhs
    }
}

impl<const LIMBS: usize> Rem<NonZero<Uint<LIMBS>>> for Uint<LIMBS> {
    type Output = Uint<LIMBS>;

    fn rem(self, rhs: NonZero<Uint<LIMBS>>) -> Self::Output {
        Self::rem_vartime(&self, &rhs)
    }
}

impl<const LIMBS: usize> RemAssign<&NonZero<Uint<LIMBS>>> for Uint<LIMBS> {
    fn rem_assign(&mut self, rhs: &NonZero<Uint<LIMBS>>) {
        *self %= *rhs
    }
}

impl<const LIMBS: usize> RemAssign<NonZero<Uint<LIMBS>>> for Uint<LIMBS> {
    fn rem_assign(&mut self, rhs: NonZero<Uint<LIMBS>>) {
        *self = *self % rhs;
    }
}

impl<const LIMBS: usize> Rem<NonZero<Uint<LIMBS>>> for Wrapping<Uint<LIMBS>> {
    type Output = Wrapping<Uint<LIMBS>>;

    fn rem(self, rhs: NonZero<Uint<LIMBS>>) -> Self::Output {
        Wrapping(self.0 % rhs)
    }
}

impl<const LIMBS: usize> Rem<NonZero<Uint<LIMBS>>> for &Wrapping<Uint<LIMBS>> {
    type Output = Wrapping<Uint<LIMBS>>;

    fn rem(self, rhs: NonZero<Uint<LIMBS>>) -> Self::Output {
        *self % rhs
    }
}

impl<const LIMBS: usize> Rem<&NonZero<Uint<LIMBS>>> for &Wrapping<Uint<LIMBS>> {
    type Output = Wrapping<Uint<LIMBS>>;

    fn rem(self, rhs: &NonZero<Uint<LIMBS>>) -> Self::Output {
        *self % *rhs
    }
}

impl<const LIMBS: usize> Rem<&NonZero<Uint<LIMBS>>> for Wrapping<Uint<LIMBS>> {
    type Output = Wrapping<Uint<LIMBS>>;

    fn rem(self, rhs: &NonZero<Uint<LIMBS>>) -> Self::Output {
        self % *rhs
    }
}

impl<const LIMBS: usize> RemAssign<NonZero<Uint<LIMBS>>> for Wrapping<Uint<LIMBS>> {
    fn rem_assign(&mut self, rhs: NonZero<Uint<LIMBS>>) {
        *self %= &rhs;
    }
}

impl<const LIMBS: usize> RemAssign<&NonZero<Uint<LIMBS>>> for Wrapping<Uint<LIMBS>> {
    fn rem_assign(&mut self, rhs: &NonZero<Uint<LIMBS>>) {
        *self = Wrapping(self.0 % rhs)
    }
}

impl<const LIMBS: usize> DivRemLimb for Uint<LIMBS> {
    fn div_rem_limb_with_reciprocal(&self, reciprocal: &Reciprocal) -> (Self, Limb) {
        Self::div_rem_limb_with_reciprocal(self, reciprocal)
    }
}

impl<const LIMBS: usize> RemLimb for Uint<LIMBS> {
    fn rem_limb_with_reciprocal(&self, reciprocal: &Reciprocal) -> Limb {
        Self::rem_limb_with_reciprocal(self, reciprocal)
    }
}

#[cfg(test)]
mod tests {
    use crate::{Limb, NonZero, Uint, Word, U128, U256, U64};

    #[cfg(feature = "rand")]
    use {
        crate::{CheckedMul, Random},
        rand_chacha::ChaChaRng,
        rand_core::RngCore,
        rand_core::SeedableRng,
    };

    #[test]
    fn div_word() {
        for (n, d, e, ee) in &[
            (200u64, 2u64, 100u64, 0),
            (100u64, 25u64, 4u64, 0),
            (100u64, 10u64, 10u64, 0),
            (1024u64, 8u64, 128u64, 0),
            (27u64, 13u64, 2u64, 1u64),
            (26u64, 13u64, 2u64, 0u64),
            (14u64, 13u64, 1u64, 1u64),
            (13u64, 13u64, 1u64, 0u64),
            (12u64, 13u64, 0u64, 12u64),
            (1u64, 13u64, 0u64, 1u64),
        ] {
            let lhs = U256::from(*n);
            let rhs = NonZero::new(U256::from(*d)).unwrap();
            let (q, r) = lhs.div_rem(&rhs);
            assert_eq!(U256::from(*e), q);
            assert_eq!(U256::from(*ee), r);
            let (q, r) = lhs.div_rem_vartime(&rhs);
            assert_eq!(U256::from(*e), q);
            assert_eq!(U256::from(*ee), r);
        }
    }

    #[cfg(feature = "rand")]
    #[test]
    fn div() {
        let mut rng = ChaChaRng::from_seed([7u8; 32]);
        for _ in 0..25 {
            let num = U256::random(&mut rng).overflowing_shr_vartime(128).unwrap();
            let den =
                NonZero::new(U256::random(&mut rng).overflowing_shr_vartime(128).unwrap()).unwrap();
            let n = num.checked_mul(den.as_ref());
            if n.is_some().into() {
                let (q, _) = n.unwrap().div_rem(&den);
                assert_eq!(q, num);
                let (q, _) = n.unwrap().div_rem_vartime(&den);
                assert_eq!(q, num);
            }
        }
    }

    #[test]
    fn div_max() {
        let mut a = U256::ZERO;
        let mut b = U256::ZERO;
        b.limbs[b.limbs.len() - 1] = Limb(Word::MAX);
        let q = a.wrapping_div(&NonZero::new(b).unwrap());
        assert_eq!(q, Uint::ZERO);
        a.limbs[a.limbs.len() - 1] = Limb(1 << (Limb::HI_BIT - 7));
        b.limbs[b.limbs.len() - 1] = Limb(0x82 << (Limb::HI_BIT - 7));
        let q = a.wrapping_div(&NonZero::new(b).unwrap());
        assert_eq!(q, Uint::ZERO);
    }

    #[test]
    fn div_one() {
        let (q, r) = U256::from(10u8).div_rem(&NonZero::new(U256::ONE).unwrap());
        assert_eq!(q, U256::from(10u8));
        assert_eq!(r, U256::ZERO);
        let (q, r) = U256::from(10u8).div_rem_vartime(&NonZero::new(U256::ONE).unwrap());
        assert_eq!(q, U256::from(10u8));
        assert_eq!(r, U256::ZERO);
    }

    #[test]
    fn div_edge() {
        let lo = U128::from_be_hex("00000000000000000000000000000001");
        let hi = U128::from_be_hex("00000000000000000000000000000001");
        let y = U128::from_be_hex("00000000000000010000000000000001");
        let x = U256::from((lo, hi));
        let expect = (U64::MAX.resize::<{ U256::LIMBS }>(), U256::from(2u64));

        let (q1, r1) = Uint::div_rem(&x, &NonZero::new(y.resize()).unwrap());
        assert_eq!((q1, r1), expect);
        let (q2, r2) = Uint::div_rem_vartime(&x, &NonZero::new(y).unwrap());
        assert_eq!((q2, r2.resize()), expect);
        let r3 = Uint::rem(&x, &NonZero::new(y.resize()).unwrap());
        assert_eq!(r3, expect.1);
        let r4 = Uint::rem_vartime(&x, &NonZero::new(y.resize()).unwrap());
        assert_eq!(r4, expect.1);
        let r5 = Uint::rem_wide_vartime((lo, hi), &NonZero::new(y).unwrap());
        assert_eq!(r5.resize(), expect.1);
    }

    #[test]
    fn reduce_one() {
        let r = U256::from(10u8).rem_vartime(&NonZero::new(U256::ONE).unwrap());
        assert_eq!(r, U256::ZERO);
    }

    #[test]
    fn reduce_tests() {
        let r = U256::from(10u8).rem_vartime(&NonZero::new(U256::from(2u8)).unwrap());
        assert_eq!(r, U256::ZERO);
        let r = U256::from(10u8).rem_vartime(&NonZero::new(U256::from(3u8)).unwrap());
        assert_eq!(r, U256::ONE);
        let r = U256::from(10u8).rem_vartime(&NonZero::new(U256::from(7u8)).unwrap());
        assert_eq!(r, U256::from(3u8));
    }

    #[test]
    fn reduce_tests_wide_zero_padded() {
        let r = U256::rem_wide_vartime(
            (U256::from(10u8), U256::ZERO),
            &NonZero::new(U256::from(2u8)).unwrap(),
        );
        assert_eq!(r, U256::ZERO);
        let r = U256::rem_wide_vartime(
            (U256::from(10u8), U256::ZERO),
            &NonZero::new(U256::from(3u8)).unwrap(),
        );
        assert_eq!(r, U256::ONE);
        let r = U256::rem_wide_vartime(
            (U256::from(10u8), U256::ZERO),
            &NonZero::new(U256::from(7u8)).unwrap(),
        );
        assert_eq!(r, U256::from(3u8));
        let r = U256::rem_wide_vartime(
            (U256::from(10u8), U256::ZERO),
            &NonZero::new(U256::MAX).unwrap(),
        );
        assert_eq!(r, U256::from(10u8));
    }

    #[test]
    fn reduce_max() {
        let mut a = U256::ZERO;
        let mut b = U256::ZERO;
        b.limbs[b.limbs.len() - 1] = Limb(Word::MAX);
        let r = a.wrapping_rem_vartime(&b);
        assert_eq!(r, Uint::ZERO);
        a.limbs[a.limbs.len() - 1] = Limb(1 << (Limb::HI_BIT - 7));
        b.limbs[b.limbs.len() - 1] = Limb(0x82 << (Limb::HI_BIT - 7));
        let r = a.wrapping_rem_vartime(&b);
        assert_eq!(r, a);
    }

    #[cfg(feature = "rand")]
    #[test]
    fn rem2krand() {
        let mut rng = ChaChaRng::from_seed([7u8; 32]);
        for _ in 0..25 {
            let num = U256::random(&mut rng);
            let k = rng.next_u32() % 256;
            let den = U256::ONE.overflowing_shl_vartime(k).unwrap();

            let a = num.rem2k_vartime(k);
            let e = num.wrapping_rem_vartime(&den);
            assert_eq!(a, e);
        }
    }

    #[allow(clippy::op_ref)]
    #[test]
    fn rem_trait() {
        let a = U256::from(10u64);
        let b = NonZero::new(U256::from(3u64)).unwrap();
        let c = U256::from(1u64);

        assert_eq!(a % b, c);
        assert_eq!(a % &b, c);
        assert_eq!(&a % b, c);
        assert_eq!(&a % &b, c);
    }
}
