//! [`Uint`] division operations.

use super::div_limb::{div_rem_limb_with_reciprocal, Reciprocal};
use crate::{CheckedDiv, CtChoice, Limb, NonZero, Uint, Word, Wrapping};
use core::ops::{Div, DivAssign, Rem, RemAssign};
use subtle::CtOption;

impl<const LIMBS: usize> Uint<LIMBS> {
    /// Computes `self` / `rhs` using a pre-made reciprocal,
    /// returns the quotient (q) and remainder (r).
    #[inline(always)]
    pub const fn ct_div_rem_limb_with_reciprocal(&self, reciprocal: &Reciprocal) -> (Self, Limb) {
        div_rem_limb_with_reciprocal(self, reciprocal)
    }

    /// Computes `self` / `rhs` using a pre-made reciprocal,
    /// returns the quotient (q) and remainder (r).
    #[inline(always)]
    pub fn div_rem_limb_with_reciprocal(
        &self,
        reciprocal: &CtOption<Reciprocal>,
    ) -> CtOption<(Self, Limb)> {
        reciprocal.map(|r| div_rem_limb_with_reciprocal(self, &r))
    }

    /// Computes `self` / `rhs`, returns the quotient (q) and remainder (r).
    /// Returns the truthy value as the third element of the tuple if `rhs != 0`,
    /// and the falsy value otherwise.
    #[inline(always)]
    pub(crate) const fn ct_div_rem_limb(&self, rhs: Limb) -> (Self, Limb, CtChoice) {
        let (reciprocal, is_some) = Reciprocal::ct_new(rhs);
        let (quo, rem) = div_rem_limb_with_reciprocal(self, &reciprocal);
        (quo, rem, is_some)
    }

    /// Computes `self` / `rhs`, returns the quotient (q) and remainder (r).
    #[inline(always)]
    pub fn div_rem_limb(&self, rhs: NonZero<Limb>) -> (Self, Limb) {
        // Guaranteed to succeed since `rhs` is nonzero.
        let (quo, rem, _is_some) = self.ct_div_rem_limb(*rhs);
        (quo, rem)
    }

    /// Computes `self` / `rhs`, returns the quotient (q), remainder (r)
    /// and the truthy value for is_some or the falsy value for is_none.
    ///
    /// NOTE: Use only if you need to access const fn. Otherwise use [`Self::div_rem`] because
    /// the value for is_some needs to be checked before using `q` and `r`.
    ///
    /// This function is constant-time with respect to both `self` and `rhs`.
    #[allow(trivial_numeric_casts)]
    pub(crate) const fn const_div_rem(&self, rhs: &Self) -> (Self, Self, CtChoice) {
        let mb = rhs.bits();
        let mut rem = *self;
        let mut quo = Self::ZERO;
        // If there is overflow, it means `mb == 0`, so `rhs == 0`.
        let (mut c, overflow) = rhs.shl(Self::BITS - mb);
        let is_some = overflow.not();

        let mut i = Self::BITS;
        let mut done = CtChoice::FALSE;
        loop {
            let (mut r, borrow) = rem.sbb(&c, Limb::ZERO);
            rem = Self::ct_select(&r, &rem, CtChoice::from_word_mask(borrow.0).or(done));
            r = quo.bitor(&Self::ONE);
            quo = Self::ct_select(&r, &quo, CtChoice::from_word_mask(borrow.0).or(done));
            if i == 0 {
                break;
            }
            i -= 1;
            // when `i < mb`, the computation is actually done, so we ensure `quo` and `rem`
            // aren't modified further (but do the remaining iterations anyway to be constant-time)
            done = CtChoice::from_word_lt(i as Word, mb as Word);
            c = c.shr1();
            quo = Self::ct_select(&quo.shl1(), &quo, done);
        }

        quo = Self::ct_select(&Self::ZERO, &quo, is_some);
        (quo, rem, is_some)
    }

    /// Computes `self` / `rhs`, returns the quotient (q), remainder (r)
    /// and the truthy value for is_some or the falsy value for is_none.
    ///
    /// NOTE: Use only if you need to access const fn. Otherwise use [`Self::div_rem`] because
    /// the value for is_some needs to be checked before using `q` and `r`.
    ///
    /// This is variable only with respect to `rhs`.
    ///
    /// When used with a fixed `rhs`, this function is constant-time with respect
    /// to `self`.
    pub(crate) const fn const_div_rem_vartime(&self, rhs: &Self) -> (Self, Self, CtChoice) {
        let mb = rhs.bits_vartime();
        let mut bd = Self::BITS - mb;
        let mut rem = *self;
        let mut quo = Self::ZERO;
        let (mut c, overflow) = rhs.shl_vartime(bd);
        let is_some = overflow.not();

        loop {
            let (mut r, borrow) = rem.sbb(&c, Limb::ZERO);
            rem = Self::ct_select(&r, &rem, CtChoice::from_word_mask(borrow.0));
            r = quo.bitor(&Self::ONE);
            quo = Self::ct_select(&r, &quo, CtChoice::from_word_mask(borrow.0));
            if bd == 0 {
                break;
            }
            bd -= 1;
            c = c.shr1();
            quo = quo.shl1();
        }

        quo = Self::ct_select(&Self::ZERO, &quo, is_some);
        (quo, rem, is_some)
    }

    /// Computes `self` % `rhs`, returns the remainder and and the truthy value for is_some or the
    /// falsy value for is_none.
    ///
    /// NOTE: Use only if you need to access const fn. Otherwise use [`Self::rem`].
    /// This is variable only with respect to `rhs`.
    ///
    /// When used with a fixed `rhs`, this function is constant-time with respect
    /// to `self`.
    ///
    /// ### Usage:
    /// ```
    /// use crypto_bigint::{U448, CtChoice, Limb};
    ///
    /// let a = U448::from(20_u64);
    /// let b = U448::from(6_u64);
    /// let (remainder, is_some) = a.const_rem(&b);
    ///
    /// // Verify the result
    /// assert_eq!(remainder, U448::from(2_u64));
    /// assert!(bool::from(is_some));
    /// ```
    pub const fn const_rem(&self, rhs: &Self) -> (Self, CtChoice) {
        let mb = rhs.bits_vartime();
        let mut bd = Self::BITS - mb;
        let mut rem = *self;
        let (mut c, overflow) = rhs.shl_vartime(bd);
        let is_some = overflow.not();

        loop {
            let (r, borrow) = rem.sbb(&c, Limb::ZERO);
            rem = Self::ct_select(&r, &rem, CtChoice::from_word_mask(borrow.0));
            if bd == 0 {
                break;
            }
            bd -= 1;
            c = c.shr1();
        }

        (rem, is_some)
    }

    /// Computes `self` % `rhs`, returns the remainder and
    /// and the truthy value for is_some or the falsy value for is_none.
    ///
    /// This is variable only with respect to `rhs`.
    ///
    /// When used with a fixed `rhs`, this function is constant-time with respect
    /// to `self`.
    ///
    /// ### Usage:
    /// ```
    /// use crypto_bigint::{U448, CtChoice};
    ///
    /// let lower = U448::from(15_u64); // Lower part of the wide integer
    /// let upper = U448::from(0_u64);  // Upper part of the wide integer
    /// let rhs = U448::from(7_u64);    // Modulus
    ///
    /// let (remainder, is_some) = U448::const_rem_wide((lower, upper), &rhs);
    ///
    /// // Verify the result
    /// assert_eq!(remainder, U448::from(1_u64));
    /// assert!(<CtChoice as Into<bool>>::into(is_some));
    /// ```
    pub const fn const_rem_wide(lower_upper: (Self, Self), rhs: &Self) -> (Self, CtChoice) {
        let mb = rhs.bits_vartime();

        // The number of bits to consider is two sets of limbs * BITS - mb (modulus bitcount)
        let mut bd = (2 * Self::BITS) - mb;

        // The wide integer to reduce, split into two halves
        let (mut lower, mut upper) = lower_upper;

        // Factor of the modulus, split into two halves
        let (mut c, _overflow) = Self::shl_vartime_wide((*rhs, Uint::ZERO), bd);

        loop {
            let (lower_sub, borrow) = lower.sbb(&c.0, Limb::ZERO);
            let (upper_sub, borrow) = upper.sbb(&c.1, borrow);

            lower = Self::ct_select(&lower_sub, &lower, CtChoice::from_word_mask(borrow.0));
            upper = Self::ct_select(&upper_sub, &upper, CtChoice::from_word_mask(borrow.0));
            if bd == 0 {
                break;
            }
            bd -= 1;
            let (new_c, _overflow) = Self::shr_vartime_wide(c, 1);
            c = new_c;
        }

        let is_some = CtChoice::from_u32_nonzero(mb);
        (lower, is_some)
    }

    /// Computes `self` % 2^k. Faster than reduce since its a power of 2.
    /// Limited to 2^16-1 since Uint doesn't support higher.
    /// TODO: this is not constant-time.
    ///
    /// ### Usage:
    /// ```
    /// use crypto_bigint::{U448, Limb};
    ///
    /// let a = U448::from(10_u64);
    /// let k = 3; // 2^3 = 8
    /// let remainder = a.rem2k(k);
    ///
    /// // As 10 % 8 = 2
    /// assert_eq!(remainder, U448::from(2_u64));
    /// ```
    pub const fn rem2k(&self, k: u32) -> Self {
        let highest = (LIMBS - 1) as u32;
        let index = k / Limb::BITS;
        let le = CtChoice::from_u32_le(index, highest);
        let limb_num = le.select_u32(highest, index) as usize;

        let base = k % Limb::BITS;
        let mask = (1 << base) - 1;
        let mut out = *self;

        let outmask = Limb(out.limbs[limb_num].0 & mask);

        out.limbs[limb_num] = Limb::ct_select(out.limbs[limb_num], outmask, le);

        // TODO: this is not constant-time.
        let mut i = limb_num + 1;
        while i < LIMBS {
            out.limbs[i] = Limb::ZERO;
            i += 1;
        }

        out
    }

    /// Computes self / rhs, returns the quotient, remainder.
    ///
    /// ### Usage:
    /// ```
    /// use crypto_bigint::{U448, NonZero};
    ///
    /// let a = U448::from(8_u64);
    /// let res = NonZero::new(U448::from(4_u64))
    ///    .map(|b| a.div_rem(&b))
    ///    .expect("Division by zero");
    ///
    /// assert_eq!(res.0, U448::from(2_u64));
    /// assert_eq!(res.1, U448::from(0_u64));
    /// ```
    pub fn div_rem(&self, rhs: &NonZero<Self>) -> (Self, Self) {
        // Since `rhs` is nonzero, this should always hold.
        let (q, r, _c) = self.const_div_rem(rhs);
        (q, r)
    }

    /// Computes self / rhs, returns the quotient, remainder. Constant-time only for fixed `rhs`.
    pub fn div_rem_vartime(&self, rhs: &NonZero<Self>) -> (Self, Self) {
        // Since `rhs` is nonzero, this should always hold.
        let (q, r, _c) = self.const_div_rem_vartime(rhs);
        (q, r)
    }

    /// Computes self % rhs, returns the remainder.
    ///
    /// ### Usage:
    /// ```
    /// use crypto_bigint::{U448, NonZero};
    ///
    /// let a = U448::from(8_u64);
    /// let remainder = NonZero::new(U448::from(3_u64))
    ///     .map(|b| a.rem(&b))
    ///     .expect("Modulo by zero");
    ///
    /// assert_eq!(remainder, U448::from(2_u64));
    /// ```
    pub fn rem(&self, rhs: &NonZero<Self>) -> Self {
        // Since `rhs` is nonzero, this should always hold.
        let (r, _c) = self.const_rem(rhs);
        r
    }

    /// Wrapped division is just normal division i.e. `self` / `rhs`
    /// There’s no way wrapping could ever happen.
    /// This function exists, so that all operations are accounted for in the wrapping operations.
    ///
    /// Panics if `rhs == 0`.
    ///
    /// ### Usage:
    /// ```
    /// use crypto_bigint::U448;
    ///
    /// let a = U448::from(10_u64);
    /// let b = U448::from(2_u64);
    /// let quotient = a.wrapping_div(&b);
    ///
    /// assert_eq!(quotient, U448::from(5_u64));
    /// ```
    pub const fn wrapping_div(&self, rhs: &Self) -> Self {
        let (q, _, c) = self.const_div_rem(rhs);
        assert!(c.is_true_vartime(), "divide by zero");
        q
    }

    /// Wrapped division is just normal division i.e. `self` / `rhs`
    /// There’s no way wrapping could ever happen.
    /// This function exists, so that all operations are accounted for in the wrapping operations.
    ///
    /// Panics if `rhs == 0`. Constant-time only for fixed `rhs`.
    pub const fn wrapping_div_vartime(&self, rhs: &Self) -> Self {
        let (q, _, c) = self.const_div_rem_vartime(rhs);
        assert!(c.is_true_vartime(), "divide by zero");
        q
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
    /// assert!(<Choice as Into<bool>>::into(a.checked_div(&zero).is_none()), "Should be None for division by zero");
    pub fn checked_div(&self, rhs: &Self) -> CtOption<Self> {
        NonZero::new(*rhs).map(|rhs| {
            let (q, _r) = self.div_rem(&rhs);
            q
        })
    }

    /// Wrapped (modular) remainder calculation is just `self` % `rhs`.
    /// There’s no way wrapping could ever happen.
    /// This function exists, so that all operations are accounted for in the wrapping operations.
    ///
    /// Panics if `rhs == 0`.
    ///
    /// ### Usage:
    /// ```
    /// use crypto_bigint::U448;
    ///
    /// let a = U448::from(10_u64);
    /// let b = U448::from(3_u64);
    /// let remainder = a.wrapping_rem(&b);
    ///
    /// assert_eq!(remainder, U448::from(1_u64));
    /// ```
    pub const fn wrapping_rem(&self, rhs: &Self) -> Self {
        let (r, c) = self.const_rem(rhs);
        assert!(c.is_true_vartime(), "modulo zero");
        r
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
    /// assert!(<Choice as Into<bool>>::into(remainder_option.is_some()), "Reduction by zero");
    ///
    /// // Check reduction by zero
    /// let zero = U448::from(0_u64);
    /// assert!(<Choice as Into<bool>>::into(a.checked_rem(&zero).is_none()), "Should be None for reduction by zero");
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
        let (q, _, _) = self.ct_div_rem_limb(*rhs);
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
        let (_, r, _) = self.ct_div_rem_limb(*rhs);
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

impl<const LIMBS: usize> CheckedDiv<Uint<LIMBS>> for Uint<LIMBS> {
    type Output = Self;

    fn checked_div(&self, rhs: Uint<LIMBS>) -> CtOption<Self> {
        self.checked_div(&rhs)
    }
}

impl<const LIMBS: usize> CheckedDiv<&Uint<LIMBS>> for Uint<LIMBS> {
    type Output = Self;

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
        Self::rem(&self, &rhs)
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

#[cfg(test)]
mod tests {
    use crate::{Limb, NonZero, Uint, Word, U256};

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
            let rhs = U256::from(*d);
            let (q, r, is_some) = lhs.const_div_rem(&rhs);
            assert!(is_some.is_true_vartime());
            assert_eq!(U256::from(*e), q);
            assert_eq!(U256::from(*ee), r);
            let (q, r, is_some) = lhs.const_div_rem_vartime(&rhs);
            assert!(is_some.is_true_vartime());
            assert_eq!(U256::from(*e), q);
            assert_eq!(U256::from(*ee), r);
        }
    }

    #[cfg(feature = "rand")]
    #[test]
    fn div() {
        let mut rng = ChaChaRng::from_seed([7u8; 32]);
        for _ in 0..25 {
            let (num, _) = U256::random(&mut rng).shr_vartime(128);
            let (den, _) = U256::random(&mut rng).shr_vartime(128);
            let n = num.checked_mul(&den);
            if n.is_some().into() {
                let (q, _, is_some) = n.unwrap().const_div_rem(&den);
                assert!(is_some.is_true_vartime());
                assert_eq!(q, num);
                let (q, _, is_some) = n.unwrap().const_div_rem_vartime(&den);
                assert!(is_some.is_true_vartime());
                assert_eq!(q, num);
            }
        }
    }

    #[test]
    fn div_max() {
        let mut a = U256::ZERO;
        let mut b = U256::ZERO;
        b.limbs[b.limbs.len() - 1] = Limb(Word::MAX);
        let q = a.wrapping_div(&b);
        assert_eq!(q, Uint::ZERO);
        a.limbs[a.limbs.len() - 1] = Limb(1 << (Limb::HI_BIT - 7));
        b.limbs[b.limbs.len() - 1] = Limb(0x82 << (Limb::HI_BIT - 7));
        let q = a.wrapping_div(&b);
        assert_eq!(q, Uint::ZERO);
    }

    #[test]
    fn div_zero() {
        let (q, r, is_some) = U256::ONE.const_div_rem(&U256::ZERO);
        assert!(!is_some.is_true_vartime());
        assert_eq!(q, U256::ZERO);
        assert_eq!(r, U256::ONE);
        let (q, r, is_some) = U256::ONE.const_div_rem_vartime(&U256::ZERO);
        assert!(!is_some.is_true_vartime());
        assert_eq!(q, U256::ZERO);
        assert_eq!(r, U256::ONE);
    }

    #[test]
    fn div_one() {
        let (q, r, is_some) = U256::from(10u8).const_div_rem(&U256::ONE);
        assert!(is_some.is_true_vartime());
        assert_eq!(q, U256::from(10u8));
        assert_eq!(r, U256::ZERO);
        let (q, r, is_some) = U256::from(10u8).const_div_rem_vartime(&U256::ONE);
        assert!(is_some.is_true_vartime());
        assert_eq!(q, U256::from(10u8));
        assert_eq!(r, U256::ZERO);
    }

    #[test]
    fn reduce_one() {
        let (r, is_some) = U256::from(10u8).const_rem(&U256::ONE);
        assert!(is_some.is_true_vartime());
        assert_eq!(r, U256::ZERO);
    }

    #[test]
    fn reduce_zero() {
        let u = U256::from(10u8);
        let (r, is_some) = u.const_rem(&U256::ZERO);
        assert!(!is_some.is_true_vartime());
        assert_eq!(r, u);
    }

    #[test]
    fn reduce_tests() {
        let (r, is_some) = U256::from(10u8).const_rem(&U256::from(2u8));
        assert!(is_some.is_true_vartime());
        assert_eq!(r, U256::ZERO);
        let (r, is_some) = U256::from(10u8).const_rem(&U256::from(3u8));
        assert!(is_some.is_true_vartime());
        assert_eq!(r, U256::ONE);
        let (r, is_some) = U256::from(10u8).const_rem(&U256::from(7u8));
        assert!(is_some.is_true_vartime());
        assert_eq!(r, U256::from(3u8));
    }

    #[test]
    fn reduce_tests_wide_zero_padded() {
        let (r, is_some) = U256::const_rem_wide((U256::from(10u8), U256::ZERO), &U256::from(2u8));
        assert!(is_some.is_true_vartime());
        assert_eq!(r, U256::ZERO);
        let (r, is_some) = U256::const_rem_wide((U256::from(10u8), U256::ZERO), &U256::from(3u8));
        assert!(is_some.is_true_vartime());
        assert_eq!(r, U256::ONE);
        let (r, is_some) = U256::const_rem_wide((U256::from(10u8), U256::ZERO), &U256::from(7u8));
        assert!(is_some.is_true_vartime());
        assert_eq!(r, U256::from(3u8));
    }

    #[test]
    fn reduce_max() {
        let mut a = U256::ZERO;
        let mut b = U256::ZERO;
        b.limbs[b.limbs.len() - 1] = Limb(Word::MAX);
        let r = a.wrapping_rem(&b);
        assert_eq!(r, Uint::ZERO);
        a.limbs[a.limbs.len() - 1] = Limb(1 << (Limb::HI_BIT - 7));
        b.limbs[b.limbs.len() - 1] = Limb(0x82 << (Limb::HI_BIT - 7));
        let r = a.wrapping_rem(&b);
        assert_eq!(r, a);
    }

    #[cfg(feature = "rand")]
    #[test]
    fn rem2krand() {
        let mut rng = ChaChaRng::from_seed([7u8; 32]);
        for _ in 0..25 {
            let num = U256::random(&mut rng);
            let k = rng.next_u32() % 256;
            let (den, _) = U256::ONE.shl_vartime(k);

            let a = num.rem2k(k);
            let e = num.wrapping_rem(&den);
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
