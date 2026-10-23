//! [`Uint`] division operations.

use super::div_limb::Reciprocal;
use crate::{
    CheckedDiv, Choice, CtOption, Div, DivAssign, DivRemLimb, DivVartime, Limb, NonZero, Rem,
    RemAssign, RemLimb, RemMixed, ToUnsigned, Uint, UintRef, Unsigned, Wrapping,
};

impl<const LIMBS: usize> Uint<LIMBS> {
    /// Computes `self / rhs` using a pre-made reciprocal, returning the quotient
    /// and remainder.
    #[must_use]
    pub const fn div_rem_limb_with_reciprocal(&self, reciprocal: &Reciprocal) -> (Self, Limb) {
        let mut quo = *self;
        let rem = quo
            .as_mut_uint_ref()
            .div_rem_limb_with_reciprocal(reciprocal);
        (quo, rem)
    }

    /// Computes `self / rhs`, returning the quotient and remainder.
    #[must_use]
    pub const fn div_rem_limb(&self, rhs: NonZero<Limb>) -> (Self, Limb) {
        let mut quo = *self;
        let rem = quo.as_mut_uint_ref().div_rem_limb(rhs);
        (quo, rem)
    }

    /// Computes `self % rhs` using a pre-made reciprocal.
    #[must_use]
    pub const fn rem_limb_with_reciprocal(&self, reciprocal: &Reciprocal) -> Limb {
        self.as_uint_ref()
            .rem_limb_with_reciprocal(reciprocal, Limb::ZERO)
    }

    /// Computes `self % rhs` for a `Limb`-sized divisor.
    #[must_use]
    pub const fn rem_limb(&self, rhs: NonZero<Limb>) -> Limb {
        self.as_uint_ref().rem_limb(rhs)
    }

    /// Computes `self` / `rhs`, returning the quotient and the remainder.
    ///
    /// This function is constant-time with respect to both `self` and `rhs`.
    #[must_use]
    pub const fn div_rem<const RHS_LIMBS: usize>(
        &self,
        rhs: &NonZero<Uint<RHS_LIMBS>>,
    ) -> (Self, Uint<RHS_LIMBS>) {
        let (mut x, mut y) = (*self, *rhs.as_ref());
        UintRef::div_rem(x.as_mut_uint_ref(), y.as_mut_uint_ref());
        (x, y)
    }

    /// Computes `self` / `rhs`, returning the quotient and the remainder.
    ///
    /// This is variable-time only with respect to `rhs`.
    ///
    /// When used with a fixed `rhs`, this function is constant-time with respect
    /// to `self`.
    #[inline]
    #[must_use]
    pub const fn div_rem_vartime<const RHS_LIMBS: usize>(
        &self,
        rhs: &NonZero<Uint<RHS_LIMBS>>,
    ) -> (Self, Uint<RHS_LIMBS>) {
        let (mut x, mut y) = (*self, *rhs.as_ref());
        UintRef::div_rem_vartime(x.as_mut_uint_ref(), y.as_mut_uint_ref());
        (x, y)
    }

    /// Exactly divides `self` by `rhs`, returning `CtOption::none()` if `self` is not divisible by `rhs`.
    #[must_use]
    pub const fn div_exact<const RHS_LIMBS: usize>(
        &self,
        rhs: &NonZero<Uint<RHS_LIMBS>>,
    ) -> CtOption<Self> {
        let mut quo = *self;
        let mut div = rhs.get_copy();
        let exact = quo.as_mut_uint_ref().div_exact(div.as_mut_uint_ref());
        CtOption::new(quo, exact)
    }

    /// Exactly divides `self` by `rhs`, returning `CtOption::none()` if `self` is not divisible by `rhs`.
    ///
    /// This is variable-time only with respect to `rhs`.
    ///
    /// When used with a fixed `rhs`, this function is constant-time with respect to `self`.
    #[must_use]
    pub const fn div_exact_vartime<const RHS_LIMBS: usize>(
        &self,
        rhs: &NonZero<Uint<RHS_LIMBS>>,
    ) -> CtOption<Self> {
        let mut quo = *self;
        let mut div = rhs.get_copy();
        let exact = quo
            .as_mut_uint_ref()
            .div_exact_vartime(div.as_mut_uint_ref());
        CtOption::new(quo, exact)
    }

    /// Computes self / rhs, assigning the quotient to `self` and returning the remainder.
    #[must_use]
    pub(crate) fn div_rem_assign<Rhs: Unsigned>(&mut self, rhs: NonZero<Rhs>) -> Rhs {
        let mut rem = rhs.get();
        self.as_mut_uint_ref().div_rem(rem.as_mut_uint_ref());
        rem
    }

    /// Computes `self` % `rhs`.
    #[must_use]
    pub const fn rem<const RHS_LIMBS: usize>(
        &self,
        rhs: &NonZero<Uint<RHS_LIMBS>>,
    ) -> Uint<RHS_LIMBS> {
        let (mut x, mut y) = (*self, *rhs.as_ref());
        UintRef::div_rem(x.as_mut_uint_ref(), y.as_mut_uint_ref());
        y
    }

    /// Computes `self` % `rhs` in variable-time with respect to `rhs`.
    ///
    /// When used with a fixed `rhs`, this function is constant-time with respect
    /// to `self`.
    #[inline]
    #[must_use]
    pub const fn rem_vartime<const RHS_LIMBS: usize>(
        &self,
        rhs: &NonZero<Uint<RHS_LIMBS>>,
    ) -> Uint<RHS_LIMBS> {
        let (mut x, mut y) = (*self, *rhs.as_ref());
        UintRef::div_rem_vartime(x.as_mut_uint_ref(), y.as_mut_uint_ref());
        y
    }

    /// Computes `self` % `rhs` for a double-width `Uint`.
    #[inline]
    #[must_use]
    pub const fn rem_wide(mut lower_upper: (Self, Self), rhs: &NonZero<Self>) -> Self {
        let mut y = *rhs.as_ref();
        UintRef::rem_wide(
            (
                lower_upper.0.as_mut_uint_ref(),
                lower_upper.1.as_mut_uint_ref(),
            ),
            y.as_mut_uint_ref(),
        );
        y
    }

    /// Computes `self` % `rhs`.
    ///
    /// This is variable-time only with respect to `rhs`.
    ///
    /// When used with a fixed `rhs`, this function is constant-time with respect
    /// to `self`.
    #[inline]
    #[must_use]
    pub const fn rem_wide_vartime(mut lower_upper: (Self, Self), rhs: &NonZero<Self>) -> Self {
        let mut y = *rhs.as_ref();
        UintRef::rem_wide_vartime(
            (
                lower_upper.0.as_mut_uint_ref(),
                lower_upper.1.as_mut_uint_ref(),
            ),
            y.as_mut_uint_ref(),
        );
        y
    }

    /// Computes `(lo + hi * 2^Self::BITS) / rhs` for a double-width dividend, returning the
    /// wrapped quotient, the remainder, and a [`Choice`] that is truthy when the quotient fit in
    /// `Self` without truncation.
    ///
    /// The quotient of such a dividend may exceed `Self::BITS`; only its low `Self::BITS` bits are
    /// returned (i.e. the quotient is reduced modulo `2^Self::BITS`), which is why the name is
    /// prefixed with `wrapping`. The returned [`Choice`] is truthy exactly when no wrapping
    /// occurred, i.e. when the high half of the dividend is less than `rhs`. This is the
    /// quotient-tracking counterpart of [`Uint::rem_wide`], and avoids widening the operands via
    /// [`Concat`][`crate::Concat`], so it is available for any limb count.
    ///
    /// ### Usage:
    /// ```
    /// use crypto_bigint::{U256, NonZero};
    ///
    /// // dividend = 3 * 2^256 + 5, so dividing by 3 gives quotient 2^256 + 1, remainder 2
    /// let lo = U256::from(5u64);
    /// let hi = U256::from(3u64);
    /// let rhs = NonZero::new(U256::from(3u64)).unwrap();
    /// let (quo, rem, fits) = U256::wrapping_div_rem_wide((lo, hi), &rhs);
    ///
    /// // the true quotient 2^256 + 1 doesn't fit in 256 bits, so it wraps down to 1
    /// assert_eq!(quo, U256::ONE);
    /// assert_eq!(rem, U256::from(2u64));
    /// assert!(!bool::from(fits));
    /// ```
    #[inline]
    #[must_use]
    pub const fn wrapping_div_rem_wide(
        lower_upper: (Self, Self),
        rhs: &NonZero<Self>,
    ) -> (Self, Self, Choice) {
        let (mut lo, mut hi) = lower_upper;
        let mut y = *rhs.as_ref();
        let mut quo = Self::ZERO;
        let fits = UintRef::wrapping_div_rem_wide(
            (lo.as_mut_uint_ref(), hi.as_mut_uint_ref()),
            y.as_mut_uint_ref(),
            quo.as_mut_uint_ref(),
        );
        (quo, y, fits)
    }

    /// Computes the wrapped quotient `(lo + hi * 2^Self::BITS) / rhs`, reduced modulo
    /// `2^Self::BITS`.
    ///
    /// The quotient-only counterpart of [`Uint::rem_wide`]; see [`Uint::wrapping_div_rem_wide`]
    /// for details.
    #[inline]
    #[must_use]
    pub const fn wrapping_div_wide(lower_upper: (Self, Self), rhs: &NonZero<Self>) -> Self {
        Self::wrapping_div_rem_wide(lower_upper, rhs).0
    }

    /// Exactly divides the double-width dividend `(lo, hi)` by `rhs`, returning the quotient in a
    /// [`CtOption`] that is [`none`][`CtOption::none()`] unless the division is exact *and* the
    /// quotient fits in `Self`.
    ///
    /// The quotient of a double-width dividend may exceed `Self::BITS` even when the division is
    /// exact (e.g. `2^Self::BITS / 1`), so a zero remainder alone is not sufficient: the result is
    /// only present when the true quotient is also representable in `Self`. This is the wide
    /// counterpart of [`Uint::div_exact`].
    ///
    /// ### Usage:
    /// ```
    /// use crypto_bigint::{U256, NonZero};
    ///
    /// let rhs = NonZero::new(U256::from(3u64)).unwrap();
    ///
    /// // 15 = 3 * 5 exactly
    /// let quo = U256::div_wide_exact((U256::from(15u64), U256::ZERO), &rhs).unwrap();
    /// assert_eq!(quo, U256::from(5u64));
    ///
    /// // 16 is not divisible by 3
    /// let not_exact = U256::div_wide_exact((U256::from(16u64), U256::ZERO), &rhs);
    /// assert!(bool::from(not_exact.is_none()));
    ///
    /// // 2^256 is divisible by 1, but the quotient 2^256 does not fit in `U256`
    /// let one = NonZero::new(U256::ONE).unwrap();
    /// let overflows = U256::div_wide_exact((U256::ZERO, U256::ONE), &one);
    /// assert!(bool::from(overflows.is_none()));
    /// ```
    #[inline]
    #[must_use]
    pub const fn div_wide_exact(lower_upper: (Self, Self), rhs: &NonZero<Self>) -> CtOption<Self> {
        let (quo, rem, fits) = Self::wrapping_div_rem_wide(lower_upper, rhs);
        CtOption::new(quo, rem.is_zero().and(fits))
    }

    /// Computes `(lo + hi * 2^Self::BITS) / rhs` for a double-width dividend, returning the
    /// wrapped quotient, the remainder, and a [`Choice`] that is truthy when the quotient fit in
    /// `Self` without truncation.
    ///
    /// This is variable-time only with respect to `rhs`. When used with a fixed `rhs`, it is
    /// constant-time with respect to the dividend. See [`Uint::wrapping_div_rem_wide`] for details.
    #[inline]
    #[must_use]
    pub const fn wrapping_div_rem_wide_vartime(
        lower_upper: (Self, Self),
        rhs: &NonZero<Self>,
    ) -> (Self, Self, Choice) {
        let (mut lo, mut hi) = lower_upper;
        let mut y = *rhs.as_ref();
        let mut quo = Self::ZERO;
        let fits = UintRef::wrapping_div_rem_wide_vartime(
            (lo.as_mut_uint_ref(), hi.as_mut_uint_ref()),
            y.as_mut_uint_ref(),
            quo.as_mut_uint_ref(),
        );
        (quo, y, fits)
    }

    /// Computes the wrapped quotient `(lo + hi * 2^Self::BITS) / rhs`, reduced modulo
    /// `2^Self::BITS`.
    ///
    /// This is variable-time only with respect to `rhs`. See [`Uint::wrapping_div_wide`].
    #[inline]
    #[must_use]
    pub const fn wrapping_div_wide_vartime(lower_upper: (Self, Self), rhs: &NonZero<Self>) -> Self {
        Self::wrapping_div_rem_wide_vartime(lower_upper, rhs).0
    }

    /// Exactly divides the double-width dividend `(lo, hi)` by `rhs`, returning the quotient in a
    /// [`CtOption`] that is [`none`][`CtOption::none()`] unless the division is exact *and* the
    /// quotient fits in `Self`.
    ///
    /// This is variable-time only with respect to `rhs`. See [`Uint::div_wide_exact`].
    #[inline]
    #[must_use]
    pub const fn div_wide_exact_vartime(
        lower_upper: (Self, Self),
        rhs: &NonZero<Self>,
    ) -> CtOption<Self> {
        let (quo, rem, fits) = Self::wrapping_div_rem_wide_vartime(lower_upper, rhs);
        CtOption::new(quo, rem.is_zero().and(fits))
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
    #[must_use]
    pub const fn rem2k_vartime(&self, k: u32) -> Self {
        self.restrict_bits(k)
    }

    /// Wrapped division is just normal division i.e. `self` / `rhs`.
    ///
    /// There’s no way wrapping could ever happen.
    /// This function exists, so that all operations are accounted for in the wrapping operations.
    #[must_use]
    pub const fn wrapping_div(&self, rhs: &NonZero<Self>) -> Self {
        self.div_rem(rhs).0
    }

    /// Wrapped division is just normal division i.e. `self` / `rhs`.
    ///
    /// There’s no way wrapping could ever happen.
    /// This function exists, so that all operations are accounted for in the wrapping operations.
    #[must_use]
    pub const fn wrapping_div_vartime<const RHS: usize>(&self, rhs: &NonZero<Uint<RHS>>) -> Self {
        self.div_rem_vartime(rhs).0
    }

    /// Perform checked division, returning a [`CtOption`] which `is_some`
    /// only if the rhs != 0.
    ///
    /// ### Usage:
    /// ```
    /// use crypto_bigint::{U448, NonZero};
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
    /// assert!(a.checked_div(&zero).is_none().to_bool(), "should be None for division by zero");
    /// ```
    #[must_use]
    pub fn checked_div<const RHS_LIMBS: usize>(&self, rhs: &Uint<RHS_LIMBS>) -> CtOption<Self> {
        NonZero::new(*rhs).map(|rhs| self.div_rem(&rhs).0)
    }

    /// This function exists, so that all operations are accounted for in the wrapping operations.
    ///
    /// # Panics
    /// - if `rhs == 0`.
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
    #[must_use]
    pub const fn wrapping_rem_vartime(&self, rhs: &Self) -> Self {
        let nz_rhs = rhs.to_nz().expect_copied("non-zero divisor");
        self.rem_vartime(&nz_rhs)
    }

    /// Perform checked reduction, returning a [`CtOption`] which `is_some`
    /// only if the rhs != 0
    ///
    /// ### Usage:
    /// ```
    /// use crypto_bigint::{U448, NonZero};
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
    /// assert!(a.checked_rem(&zero).is_none().to_bool(), "should be None for reduction by zero");
    /// ```
    #[must_use]
    pub fn checked_rem<const RHS_LIMBS: usize>(
        &self,
        rhs: &Uint<RHS_LIMBS>,
    ) -> CtOption<Uint<RHS_LIMBS>> {
        NonZero::new(*rhs).map(|rhs| self.rem(&rhs))
    }
}

impl<const LIMBS: usize, const RHS_LIMBS: usize> CheckedDiv<Uint<RHS_LIMBS>> for Uint<LIMBS> {
    fn checked_div(&self, rhs: &Uint<RHS_LIMBS>) -> CtOption<Self> {
        self.checked_div(rhs)
    }
}

impl<const LIMBS: usize, Rhs: Unsigned> Div<Rhs> for &Uint<LIMBS> {
    type Output = Uint<LIMBS>;

    #[inline]
    fn div(self, rhs: Rhs) -> Self::Output {
        *self / rhs
    }
}

impl<const LIMBS: usize, Rhs: Unsigned> Div<Rhs> for Uint<LIMBS> {
    type Output = Uint<LIMBS>;

    #[inline]
    fn div(self, rhs: Rhs) -> Self::Output {
        self / NonZero::new(rhs).expect("attempt to divide with a divisor of zero")
    }
}

impl<const LIMBS: usize, Rhs: ToUnsigned + ?Sized> Div<&NonZero<Rhs>> for &Uint<LIMBS> {
    type Output = Uint<LIMBS>;

    fn div(self, rhs: &NonZero<Rhs>) -> Self::Output {
        let mut quo = *self;
        let _rem = quo.div_rem_assign(rhs.to_unsigned());
        quo
    }
}

impl<const LIMBS: usize, Rhs: ToUnsigned + ?Sized> Div<&NonZero<Rhs>> for Uint<LIMBS> {
    type Output = Self;

    fn div(mut self, rhs: &NonZero<Rhs>) -> Self::Output {
        let _rem = self.div_rem_assign(rhs.to_unsigned());
        self
    }
}

impl<const LIMBS: usize, Rhs: Unsigned> Div<NonZero<Rhs>> for &Uint<LIMBS> {
    type Output = Uint<LIMBS>;

    fn div(self, rhs: NonZero<Rhs>) -> Self::Output {
        let mut quo = *self;
        let _rem = quo.div_rem_assign(rhs);
        quo
    }
}

impl<const LIMBS: usize, Rhs: Unsigned> Div<NonZero<Rhs>> for Uint<LIMBS> {
    type Output = Self;

    fn div(mut self, rhs: NonZero<Rhs>) -> Self::Output {
        let _rem = self.div_rem_assign(rhs);
        self
    }
}

impl<const LIMBS: usize, Rhs: ToUnsigned + ?Sized> DivAssign<&NonZero<Rhs>> for Uint<LIMBS> {
    fn div_assign(&mut self, rhs: &NonZero<Rhs>) {
        let _rem = self.div_rem_assign(rhs.to_unsigned());
    }
}

impl<const LIMBS: usize, Rhs: Unsigned> DivAssign<NonZero<Rhs>> for Uint<LIMBS> {
    fn div_assign(&mut self, rhs: NonZero<Rhs>) {
        let _rem = self.div_rem_assign(rhs);
    }
}

impl<const LIMBS: usize, Rhs: Unsigned> Div<NonZero<Rhs>> for Wrapping<Uint<LIMBS>> {
    type Output = Self;

    fn div(self, rhs: NonZero<Rhs>) -> Self::Output {
        Wrapping(self.0 / rhs)
    }
}

impl<const LIMBS: usize, Rhs: Unsigned> Div<NonZero<Rhs>> for &Wrapping<Uint<LIMBS>> {
    type Output = Wrapping<Uint<LIMBS>>;

    fn div(self, rhs: NonZero<Rhs>) -> Self::Output {
        Wrapping(self.0 / rhs)
    }
}

impl<const LIMBS: usize, Rhs: ToUnsigned + ?Sized> Div<&NonZero<Rhs>> for &Wrapping<Uint<LIMBS>> {
    type Output = Wrapping<Uint<LIMBS>>;

    fn div(self, rhs: &NonZero<Rhs>) -> Self::Output {
        Wrapping(self.0 / rhs)
    }
}

impl<const LIMBS: usize, Rhs: ToUnsigned + ?Sized> Div<&NonZero<Rhs>> for Wrapping<Uint<LIMBS>> {
    type Output = Self;

    fn div(self, rhs: &NonZero<Rhs>) -> Self::Output {
        Wrapping(self.0 / rhs)
    }
}

impl<const LIMBS: usize, Rhs: ToUnsigned + ?Sized> DivAssign<&NonZero<Rhs>>
    for Wrapping<Uint<LIMBS>>
{
    fn div_assign(&mut self, rhs: &NonZero<Rhs>) {
        self.0 /= rhs;
    }
}

impl<const LIMBS: usize, Rhs: Unsigned> DivAssign<NonZero<Rhs>> for Wrapping<Uint<LIMBS>> {
    fn div_assign(&mut self, rhs: NonZero<Rhs>) {
        self.0 /= rhs;
    }
}

impl<const LIMBS: usize> DivVartime for Uint<LIMBS> {
    fn div_vartime(&self, rhs: &NonZero<Uint<LIMBS>>) -> Self {
        self.div_rem_vartime(rhs).0
    }
}

impl<const LIMBS: usize, Rhs: Unsigned> Rem<Rhs> for &Uint<LIMBS> {
    type Output = Rhs;

    #[inline]
    fn rem(self, rhs: Rhs) -> Self::Output {
        *self % rhs
    }
}

impl<const LIMBS: usize, Rhs: Unsigned> Rem<Rhs> for Uint<LIMBS> {
    type Output = Rhs;

    #[inline]
    fn rem(self, rhs: Rhs) -> Self::Output {
        self % NonZero::new(rhs).expect("attempt to calculate the remainder with a divisor of zero")
    }
}

impl<const LIMBS: usize, Rhs: ToUnsigned + ?Sized> Rem<&NonZero<Rhs>> for &Uint<LIMBS> {
    type Output = Rhs::Unsigned;

    #[inline]
    fn rem(self, rhs: &NonZero<Rhs>) -> Self::Output {
        (*self).rem(rhs)
    }
}

impl<const LIMBS: usize, Rhs: ToUnsigned + ?Sized> Rem<&NonZero<Rhs>> for Uint<LIMBS> {
    type Output = Rhs::Unsigned;

    #[inline]
    fn rem(mut self, rhs: &NonZero<Rhs>) -> Self::Output {
        self.div_rem_assign(rhs.to_unsigned())
    }
}

impl<const LIMBS: usize, Rhs: Unsigned> Rem<NonZero<Rhs>> for &Uint<LIMBS> {
    type Output = Rhs;

    #[inline]
    fn rem(self, rhs: NonZero<Rhs>) -> Self::Output {
        (*self).rem(rhs)
    }
}

impl<const LIMBS: usize, Rhs: Unsigned> Rem<NonZero<Rhs>> for Uint<LIMBS> {
    type Output = Rhs;

    #[inline]
    fn rem(mut self, rhs: NonZero<Rhs>) -> Self::Output {
        self.div_rem_assign(rhs)
    }
}

impl<const LIMBS: usize, Rhs: Unsigned> Rem<NonZero<Rhs>> for Wrapping<Uint<LIMBS>> {
    type Output = Wrapping<Rhs>;

    fn rem(self, rhs: NonZero<Rhs>) -> Self::Output {
        Wrapping(self.0 % rhs)
    }
}

impl<const LIMBS: usize, Rhs: Unsigned> Rem<NonZero<Rhs>> for &Wrapping<Uint<LIMBS>> {
    type Output = Wrapping<Rhs>;

    fn rem(self, rhs: NonZero<Rhs>) -> Self::Output {
        *self % rhs
    }
}

impl<const LIMBS: usize, Rhs: ToUnsigned + ?Sized> Rem<&NonZero<Rhs>> for &Wrapping<Uint<LIMBS>> {
    type Output = Wrapping<Rhs::Unsigned>;

    fn rem(self, rhs: &NonZero<Rhs>) -> Self::Output {
        *self % rhs.to_unsigned()
    }
}

impl<const LIMBS: usize, Rhs: ToUnsigned + ?Sized> Rem<&NonZero<Rhs>> for Wrapping<Uint<LIMBS>> {
    type Output = Wrapping<Rhs::Unsigned>;

    fn rem(self, rhs: &NonZero<Rhs>) -> Self::Output {
        self % rhs.to_unsigned()
    }
}

impl<const LIMBS: usize, Rhs: Unsigned> RemAssign<NonZero<Rhs>> for Uint<LIMBS> {
    fn rem_assign(&mut self, rhs: NonZero<Rhs>) {
        let rem = *self % rhs;
        *self = rem.as_uint_ref().to_uint_resize();
    }
}

impl<const LIMBS: usize, Rhs: ToUnsigned + ?Sized> RemAssign<&NonZero<Rhs>> for Uint<LIMBS> {
    fn rem_assign(&mut self, rhs: &NonZero<Rhs>) {
        *self %= rhs.to_unsigned();
    }
}

impl<const LIMBS: usize, Rhs: Unsigned> RemAssign<NonZero<Rhs>> for Wrapping<Uint<LIMBS>> {
    fn rem_assign(&mut self, rhs: NonZero<Rhs>) {
        *self %= &rhs;
    }
}

impl<const LIMBS: usize, Rhs: ToUnsigned + ?Sized> RemAssign<&NonZero<Rhs>>
    for Wrapping<Uint<LIMBS>>
{
    fn rem_assign(&mut self, rhs: &NonZero<Rhs>) {
        self.0 %= rhs;
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

impl<const LIMBS: usize, Rhs: Unsigned> RemMixed<Rhs> for Uint<LIMBS> {
    fn rem_mixed(&self, reductor: &NonZero<Rhs>) -> Rhs {
        let (mut quo, mut rem) = (*self, reductor.as_ref().clone());
        quo.as_mut_uint_ref().div_rem(rem.as_mut_uint_ref());
        rem
    }
}

#[cfg(test)]
#[allow(clippy::integer_division_remainder_used, reason = "test")]
mod tests {
    use crate::{
        CtAssign, DivVartime, Limb, NonZero, One, RemMixed, U64, U128, U256, U512, U896, U1024,
        Uint, Word, Wrapping, Zero,
    };

    #[cfg(feature = "rand_core")]
    use {
        crate::{Random, U192, U384},
        chacha20::ChaCha8Rng,
        rand_core::{Rng, SeedableRng},
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
            let q = lhs.div_exact(&rhs).into_option();
            assert_eq!(if *ee == 0 { Some(U256::from(*e)) } else { None }, q);
            let q = lhs.div_exact_vartime(&rhs).into_option();
            assert_eq!(if *ee == 0 { Some(U256::from(*e)) } else { None }, q);
        }
    }

    #[cfg(feature = "rand_core")]
    #[test]
    fn div() {
        let mut rng = ChaCha8Rng::from_seed([7u8; 32]);
        for _ in 0..25 {
            let num = U256::random_from_rng(&mut rng)
                .overflowing_shr_vartime(128)
                .unwrap();
            let den = NonZero::new(
                U256::random_from_rng(&mut rng)
                    .overflowing_shr_vartime(128)
                    .unwrap(),
            )
            .unwrap();
            let n = num.checked_mul(den.as_ref());
            if n.is_some().into() {
                let n = n.unwrap();
                let (q, _) = n.div_rem(&den);
                assert_eq!(q, num);
                let (q, _) = n.div_rem_vartime(&den);
                assert_eq!(q, num);
                let q = n.div_exact(&den).into_option();
                assert_eq!(q, Some(num));
                let q = n.div_exact_vartime(&den).into_option();
                assert_eq!(q, Some(num));
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
        let b = NonZero::new(b).unwrap();
        let q = a.wrapping_div(&b);
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
        let r5 = Uint::rem_wide((lo, hi), &NonZero::new(y).unwrap());
        assert_eq!(r5.resize(), expect.1);
        let r6 = Uint::rem_wide_vartime((lo, hi), &NonZero::new(y).unwrap());
        assert_eq!(r6.resize(), expect.1);
    }

    #[test]
    fn div_rem_larger_denominator() {
        // 1 = len(x) < len(y) and x < y
        let x = U64::from_be_hex("8000000000000000");
        let y = U128::from_be_hex("00000000000000010000000000000000")
            .to_nz()
            .unwrap();
        let (quo, rem) = x.div_rem(&y);
        assert_eq!(quo, Uint::ZERO);
        assert_eq!(rem, x.resize());

        // 1 = len(x) < len(y) and x > y
        let x = U64::from_be_hex("8000000000000000");
        let y = U128::from_be_hex("00000000000000000000000000001000")
            .to_nz()
            .unwrap();
        let (quo, rem) = x.div_rem(&y);
        assert_eq!(quo, U64::from_be_hex("0008000000000000"));
        assert_eq!(rem, U128::ZERO);

        // 2 = len(x) < len(y) and x < y
        let x = U128::from_be_hex("80000000000000008000000000000000");
        let y =
            U256::from_be_hex("0000000000000001000000000000000000000000000000010000000000000000")
                .to_nz()
                .unwrap();
        let (quo, rem) = x.div_rem(&y);
        assert_eq!(quo, U128::ZERO);
        assert_eq!(rem, x.resize());

        // 2 = len(x) < len(y) and x > y
        let x = U128::from_be_hex("80000000000000008000000000000000");
        let y =
            U256::from_be_hex("0000000000000000000000000000000000000000000000000000000000110000")
                .to_nz()
                .unwrap();
        let (quo, rem) = x.div_rem(&y);
        assert_eq!(quo, U128::from_be_hex("000007878787878787878f0f0f0f0f0f"));
        assert_eq!(
            rem,
            U256::from_be_hex("0000000000000000000000000000000000000000000000000000000000010000",)
        );
    }

    #[test]
    fn div_rem_larger_numerator() {
        let denom = U128::from_be_hex("AAAA0000FFFF11117777333344449999");
        let (full_q, full_r) =
            U1024::MAX.div_rem(&denom.resize::<{ U1024::LIMBS }>().to_nz().unwrap());

        let (q, r) = U1024::MAX.div_rem(&denom.to_nz().unwrap());
        assert_eq!(full_q, q);
        assert_eq!(full_r.resize(), r);
    }

    #[allow(clippy::op_ref)]
    #[test]
    fn div_trait() {
        let a = U256::from(10u64);
        let b = NonZero::new(U256::from(2u64)).unwrap();
        let c = U256::from(5u64);

        assert_eq!(a / b, c);
        assert_eq!(a / &b, c);
        assert_eq!(&a / b, c);
        assert_eq!(&a / &b, c);
        assert_eq!(Wrapping(a) / b, Wrapping(c));
        assert_eq!(Wrapping(a) / &b, Wrapping(c));
        assert_eq!(&Wrapping(a) / b, Wrapping(c));
        assert_eq!(&Wrapping(a) / &b, Wrapping(c));
    }

    #[allow(clippy::op_ref)]
    #[test]
    fn div_assign_trait() {
        let a = U256::from(10u64);
        let b = NonZero::new(U256::from(2u64)).unwrap();
        let c = U256::from(5u64);

        let mut res = a;
        res /= b;
        assert_eq!(res, c);
        let mut res = a;
        res /= &b;
        assert_eq!(res, c);

        let mut res = Wrapping(a);
        res /= b;
        assert_eq!(res, Wrapping(c));
        let mut res = Wrapping(a);
        res /= &b;
        assert_eq!(res, Wrapping(c));
    }

    #[should_panic]
    #[test]
    fn div_zero() {
        let _ = U256::ONE / U256::ZERO;
    }

    #[should_panic]
    #[test]
    #[allow(clippy::op_ref)]
    fn div_ref_zero() {
        let _ = &U256::ONE / U256::ZERO;
    }

    #[test]
    fn reduce_one() {
        let r = U256::from(10u8).rem_vartime(&NonZero::new(U256::ONE).unwrap());
        assert_eq!(r, U256::ZERO);
    }

    #[test]
    fn reduce_tests() {
        let tests = [
            (U256::from(2u8), 0u8),
            (U256::from(3u8), 1u8),
            (U256::from(7u8), 3u8),
            (U256::MAX, 10u8),
        ];
        for (divisor, expect) in tests {
            let r1 = U256::from(10u8).rem(&NonZero::new(divisor).unwrap());
            let r2 = U256::from(10u8).rem_vartime(&NonZero::new(divisor).unwrap());
            assert_eq!(r1, U256::from(expect));
            assert_eq!(r1, r2);
        }
    }

    #[test]
    fn reduce_tests_wide_zero_padded() {
        let tests = [
            (U256::from(2u8), 0u8),
            (U256::from(3u8), 1u8),
            (U256::from(7u8), 3u8),
            (U256::MAX, 10u8),
        ];
        for (divisor, expect) in tests {
            let r1 = U256::rem_wide(
                (U256::from(10u8), U256::ZERO),
                &NonZero::new(divisor).unwrap(),
            );
            let r2 = U256::rem_wide_vartime(
                (U256::from(10u8), U256::ZERO),
                &NonZero::new(divisor).unwrap(),
            );
            assert_eq!(r1, U256::from(expect));
            assert_eq!(r1, r2);
        }
    }

    #[test]
    fn rem_wide_corner_case() {
        let modulus = "0000000000000000000000000000000081000000000000000000000000000001";
        let modulus = NonZero::new(U256::from_be_hex(modulus)).expect("it's odd and not zero");
        let lo_hi = (
            U256::from_be_hex("1000000000000000000000000000000000000000000000000000000000000001"),
            U256::ZERO,
        );
        let rem = U256::rem_wide(lo_hi, &modulus);
        // Lower half is zero
        assert_eq!(
            &rem.to_be_bytes().as_ref()[0..16],
            U128::ZERO.to_be_bytes().as_ref()
        );
        // Upper half
        let expected = U128::from_be_hex("203F80FE03F80FE03F80FE03F80FE041");
        assert_eq!(
            &rem.to_be_bytes().as_ref()[16..],
            expected.to_be_bytes().as_ref()
        );

        let remv = U256::rem_wide_vartime(lo_hi, &modulus);
        assert_eq!(rem, remv);
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

    #[cfg(feature = "rand_core")]
    #[test]
    fn rem2krand() {
        let mut rng = ChaCha8Rng::from_seed([7u8; 32]);
        for _ in 0..25 {
            let num = U256::random_from_rng(&mut rng);
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
        assert_eq!(Wrapping(a) % b, Wrapping(c));
        assert_eq!(Wrapping(a) % &b, Wrapping(c));
        assert_eq!(&Wrapping(a) % b, Wrapping(c));
        assert_eq!(&Wrapping(a) % &b, Wrapping(c));
    }

    #[allow(clippy::op_ref)]
    #[test]
    fn rem_assign_trait() {
        let a = U256::from(10u64);
        let b = NonZero::new(U256::from(3u64)).unwrap();
        let c = U256::from(1u64);

        let mut res = a;
        res %= b;
        assert_eq!(res, c);
        let mut res = a;
        res %= &b;
        assert_eq!(res, c);

        let mut res = Wrapping(a);
        res %= b;
        assert_eq!(res, Wrapping(c));
        let mut res = Wrapping(a);
        res %= &b;
        assert_eq!(res, Wrapping(c));
    }

    #[should_panic]
    #[test]
    fn rem_zero() {
        let _ = U256::ONE % U256::ZERO;
    }

    #[should_panic]
    #[test]
    #[allow(clippy::op_ref)]
    fn rem_ref_zero() {
        let _ = &U256::ONE % U256::ZERO;
    }

    #[test]
    fn rem_mixed() {
        let x = U1024::from_be_hex(concat![
            "3740C11DB8F260753BC6B97DD2B8746D3E2694412772AC6ABD975119EE0A6190",
            "F27F6F0969BCA069D8D151031AF83EE2283CC2E3E4FADBBDB9EEDBF0B8F4C1FD",
            "51912C0D329FDC37D49176DB0A1A2D17E5E6D4F9F6B217FE9412EAA2F881F702",
            "7A831C1B06D31D3618D218D6E667DBD85BFC7B6B6B93422D52516989376AA29A",
        ]);
        let y = U128::from_u64(1234567890987654321);
        let rem = x.rem_mixed(&y.to_nz().unwrap());

        let y2: U1024 = U128::concat_mixed(&y, &U896::ZERO);
        let rem_control = x.rem(&NonZero::new(y2).unwrap());

        assert_eq!(rem.bits(), rem_control.bits());
        assert_eq!(rem.as_words(), &rem_control.as_words()[0..U128::LIMBS]);
        assert!(
            rem_control.as_words()[U128::LIMBS..]
                .iter()
                .all(|w| *w == 0)
        );
    }

    #[test]
    fn rem_mixed_even() {
        let x = U1024::from_be_hex(concat![
            "3740C11DB8F260753BC6B97DD2B8746D3E2694412772AC6ABD975119EE0A6190",
            "F27F6F0969BCA069D8D151031AF83EE2283CC2E3E4FADBBDB9EEDBF0B8F4C1FD",
            "51912C0D329FDC37D49176DB0A1A2D17E5E6D4F9F6B217FE9412EAA2F881F702",
            "7A831C1B06D31D3618D218D6E667DBD85BFC7B6B6B93422D52516989376AA29A",
        ]);
        let y = U512::from_u64(1234567890987654321);
        let rem: U512 = x.rem_mixed(&y.to_nz().unwrap());

        let y_wide = U512::concat_mixed(&y, &U512::ZERO);
        let rem_control: U1024 = x.rem(&NonZero::new(y_wide).unwrap());

        assert_eq!(rem.bits(), rem_control.bits());
        assert_eq!(rem.as_words(), &rem_control.as_words()[0..U512::LIMBS]);
        assert!(
            rem_control.as_words()[U512::LIMBS..]
                .iter()
                .all(|w| *w == 0)
        );
    }

    #[test]
    fn rem_mixed_through_traits() {
        struct A<T, U> {
            t: T,
            u: U,
        }
        impl<T, U> A<T, U>
        where
            T: RemMixed<U>,
            U: Clone + Zero + One + CtAssign,
        {
            fn reduce_t_by_u(&self) -> U {
                let rhs = &NonZero::new(self.u.clone()).unwrap();
                self.t.rem_mixed(rhs)
            }
        }

        let a = A {
            t: U1024::from(1234567890u64),
            u: U128::from(456u64),
        };
        assert_eq!(a.reduce_t_by_u(), U128::from(330u64));
    }

    #[test]
    fn div_vartime_through_traits() {
        struct A<T> {
            x: T,
            y: T,
        }
        impl<T> A<T>
        where
            T: DivVartime + Clone + Zero + One + CtAssign,
        {
            fn divide_x_by_y(&self) -> T {
                let rhs = &NonZero::new(self.y.clone()).unwrap();
                self.x.div_vartime(rhs)
            }
        }

        let a = A {
            x: U1024::from(1234567890u64),
            y: U1024::from(456u64),
        };
        assert_eq!(a.divide_x_by_y(), U1024::from(2707385u64));
    }

    /// Check the wide-division methods (constant-time and variable-time) for a dividend
    /// `lo + hi * 2^(L * Limb::BITS)` against the trusted `div_rem` reference, which divides the
    /// same value widened into `Uint<W>` (with `W == 2 * L`).
    fn check_wide_division<const L: usize, const W: usize>(
        lo: Uint<L>,
        hi: Uint<L>,
        den: NonZero<Uint<L>>,
    ) {
        let den_uint = *den.as_ref();

        // Reference: build the wide dividend and divide it with the trusted `div_rem`.
        let wide: Uint<W> = lo.concat_resize(&hi);
        let (full_q, full_r) = wide.div_rem(&den_uint.resize::<W>().to_nz().unwrap());
        let exp_q = full_q.resize::<L>();
        let exp_r = full_r.resize::<L>();
        let exact = exp_r == Uint::<L>::ZERO;
        // The quotient fits in `L` limbs exactly when its high half (the limbs dropped by the
        // wrapping division) is zero.
        let fits = full_q == exp_q.resize::<W>();

        // Both the constant-time and variable-time paths must match the reference.
        for (q, r, quo_fits) in [
            Uint::<L>::wrapping_div_rem_wide((lo, hi), &den),
            Uint::<L>::wrapping_div_rem_wide_vartime((lo, hi), &den),
        ] {
            assert_eq!(q, exp_q, "quotient: ({lo}, {hi}) / {den_uint}");
            assert_eq!(r, exp_r, "remainder: ({lo}, {hi}) / {den_uint}");
            assert_eq!(
                bool::from(quo_fits),
                fits,
                "fits: ({lo}, {hi}) / {den_uint}"
            );
        }
        assert_eq!(Uint::<L>::wrapping_div_wide((lo, hi), &den), exp_q);
        assert_eq!(Uint::<L>::wrapping_div_wide_vartime((lo, hi), &den), exp_q);

        // `div_wide_exact` yields the quotient only when the division is exact *and* it fits.
        let exact_and_fits = exact && fits;
        for maybe_quo in [
            Uint::<L>::div_wide_exact((lo, hi), &den),
            Uint::<L>::div_wide_exact_vartime((lo, hi), &den),
        ] {
            assert_eq!(bool::from(maybe_quo.is_some()), exact_and_fits);
            if exact_and_fits {
                assert_eq!(maybe_quo.unwrap(), exp_q);
            }
        }
    }

    #[test]
    fn div_rem_wide_edge() {
        let two_127 = U128::from_be_hex("80000000000000000000000000000000"); // 2^127

        // Boundary cases, each checked against the concat + `div_rem` reference.
        for (lo, hi, den) in [
            (U128::ZERO, U128::ZERO, U128::from(7u64)), // both halves zero
            (U128::from(100u64), U128::ZERO, U128::from(7u64)), // high half zero
            (U128::ZERO, U128::ONE, U128::ONE),         // divisor 1: quotient wraps
            (U128::MAX, U128::MAX, U128::MAX),          // 2^128 + 1 wraps to 1
            (U128::MAX, U128::ZERO, U128::from(2u64)),  // half-word divisor
            (two_127, U128::ONE, U128::from(3u64)),     // 3 * 2^127, single-word divisor
        ] {
            check_wide_division::<{ U128::LIMBS }, { U256::LIMBS }>(lo, hi, den.to_nz().unwrap());
        }
        // Single-word operands (LIMBS == 1).
        for (lo, hi, den) in [
            (U64::MAX, U64::MAX, U64::MAX),
            (U64::from(5u64), U64::from(9u64), U64::from(4u64)),
        ] {
            check_wide_division::<{ U64::LIMBS }, { U128::LIMBS }>(lo, hi, den.to_nz().unwrap());
        }

        // A couple of hand-computed values for extra confidence.
        // (2^256 - 1) / (2^128 - 1) = 2^128 + 1, wrapped mod 2^128 = 1, remainder 0; the true
        // quotient exceeds 2^128, so it does not fit.
        let (q, r, fits) =
            U128::wrapping_div_rem_wide((U128::MAX, U128::MAX), &U128::MAX.to_nz().unwrap());
        assert_eq!(q, U128::ONE);
        assert_eq!(r, U128::ZERO);
        assert!(!bool::from(fits));

        // 3 * 2^127 = 2^128 + 2^127 => hi = 1, lo = 2^127; the exact quotient is 2^127, which fits.
        let three = U128::from(3u64).to_nz().unwrap();
        let (q, r, fits) = U128::wrapping_div_rem_wide((two_127, U128::ONE), &three);
        assert_eq!(q, two_127);
        assert_eq!(r, U128::ZERO);
        assert!(bool::from(fits));
        assert_eq!(
            U128::div_wide_exact((two_127, U128::ONE), &three).unwrap(),
            two_127
        );

        // A zero remainder alone is not enough for `div_wide_exact`: 2^128 / 1 is exact but the
        // quotient overflows `U128`, so the result is absent.
        let one = U128::ONE.to_nz().unwrap();
        assert!(bool::from(
            U128::div_wide_exact((U128::ZERO, U128::ONE), &one).is_none()
        ));
    }

    #[cfg(feature = "rand_core")]
    #[test]
    fn div_rem_wide_vs_concat() {
        /// Random divisor with `K` significant limbs, widened to `Uint<L>` (still non-zero).
        fn narrow_nz<const K: usize, const L: usize>(rng: &mut ChaCha8Rng) -> NonZero<Uint<L>> {
            NonZero::<Uint<K>>::random_from_rng(rng)
                .as_ref()
                .resize::<L>()
                .to_nz()
                .unwrap()
        }

        let mut rng = ChaCha8Rng::from_seed([9u8; 32]);
        for _ in 0..300 {
            // Single-word path (U64 operands).
            let lo64 = U64::random_from_rng(&mut rng);
            let hi64 = U64::random_from_rng(&mut rng);
            check_wide_division::<{ U64::LIMBS }, { U128::LIMBS }>(
                lo64,
                hi64,
                NonZero::random_from_rng(&mut rng),
            );

            // Multi-limb path (U128): a full-width divisor, then a single-word-value divisor
            // (ywords == 1, which hits the div2by1 correction).
            let lo = U128::random_from_rng(&mut rng);
            let hi = U128::random_from_rng(&mut rng);
            check_wide_division::<{ U128::LIMBS }, { U256::LIMBS }>(
                lo,
                hi,
                NonZero::random_from_rng(&mut rng),
            );
            check_wide_division::<{ U128::LIMBS }, { U256::LIMBS }>(
                lo,
                hi,
                narrow_nz::<{ U64::LIMBS }, { U128::LIMBS }>(&mut rng),
            );

            // Odd limb count (U192): a full-width divisor (>= 3 significant limbs, so the tail
            // `done` masking / vartime early-break fires) and a narrower divisor.
            let lo192 = U192::random_from_rng(&mut rng);
            let hi192 = U192::random_from_rng(&mut rng);
            check_wide_division::<{ U192::LIMBS }, { U384::LIMBS }>(
                lo192,
                hi192,
                NonZero::random_from_rng(&mut rng),
            );
            check_wide_division::<{ U192::LIMBS }, { U384::LIMBS }>(
                lo192,
                hi192,
                narrow_nz::<{ U128::LIMBS }, { U192::LIMBS }>(&mut rng),
            );

            // Wider operands (U256): a full-width divisor, a single-word-value divisor, and one
            // with exactly LIMBS-1 significant limbs (fires the vartime early-break while the
            // divisor is still narrower than the dividend's high half).
            let lo256 = U256::random_from_rng(&mut rng);
            let hi256 = U256::random_from_rng(&mut rng);
            check_wide_division::<{ U256::LIMBS }, { U512::LIMBS }>(
                lo256,
                hi256,
                NonZero::random_from_rng(&mut rng),
            );
            check_wide_division::<{ U256::LIMBS }, { U512::LIMBS }>(
                lo256,
                hi256,
                narrow_nz::<{ U128::LIMBS }, { U256::LIMBS }>(&mut rng),
            );
            check_wide_division::<{ U256::LIMBS }, { U512::LIMBS }>(
                lo256,
                hi256,
                narrow_nz::<{ U192::LIMBS }, { U256::LIMBS }>(&mut rng),
            );
        }
    }
}
