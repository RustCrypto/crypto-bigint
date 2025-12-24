pub use ctutils::Choice as ConstChoice;
use subtle::CtOption;

use crate::{
    Int, Limb, NonZero, NonZeroInt, Odd, OddInt, Uint,
    modular::{ConstMontyForm, ConstMontyParams, SafeGcdInverter},
};

/// `const` equivalent of `u32::max(a, b)`.
pub const fn u32_max(a: u32, b: u32) -> u32 {
    ConstChoice::from_u32_lt(a, b).select_u32(a, b)
}

/// `const` equivalent of `u32::min(a, b)`.
pub const fn u32_min(a: u32, b: u32) -> u32 {
    ConstChoice::from_u32_lt(a, b).select_u32(b, a)
}

/// An equivalent of `subtle::CtOption` usable in a `const fn` context.
#[derive(Debug, Clone)]
pub struct ConstCtOption<T> {
    value: T,
    is_some: ConstChoice,
}

impl<T> ConstCtOption<T> {
    #[inline]
    pub(crate) const fn new(value: T, is_some: ConstChoice) -> Self {
        Self { value, is_some }
    }

    #[inline]
    pub(crate) const fn some(value: T) -> Self {
        Self {
            value,
            is_some: ConstChoice::TRUE,
        }
    }

    #[inline]
    pub(crate) const fn none(dummy_value: T) -> Self {
        Self {
            value: dummy_value,
            is_some: ConstChoice::FALSE,
        }
    }

    /// Returns a reference to the contents of this structure.
    ///
    /// **Note:** if the second element is `None`, the first value may take any value.
    #[inline]
    pub(crate) const fn components_ref(&self) -> (&T, ConstChoice) {
        // Since Rust is not smart enough to tell that we would be moving the value,
        // and hence no destructors will be called, we have to return a reference instead.
        // See https://github.com/rust-lang/rust/issues/66753
        (&self.value, self.is_some)
    }

    /// Returns a true [`ConstChoice`] if this value is `Some`.
    #[inline]
    pub const fn is_some(&self) -> ConstChoice {
        self.is_some
    }

    /// Returns a true [`ConstChoice`] if this value is `None`.
    #[inline]
    pub const fn is_none(&self) -> ConstChoice {
        self.is_some.not()
    }

    /// This returns the underlying value but panics if it is not `Some`.
    #[inline]
    #[track_caller]
    pub fn unwrap(self) -> T {
        assert!(
            self.is_some.to_bool_vartime(),
            "called `ConstCtOption::unwrap()` on a `None` value"
        );
        self.value
    }

    /// Apply an additional [`ConstChoice`] requirement to `is_some`.
    #[inline]
    pub(crate) const fn and_choice(mut self, is_some: ConstChoice) -> Self {
        self.is_some = self.is_some.and(is_some);
        self
    }
}

impl<T> From<ConstCtOption<T>> for CtOption<T> {
    #[inline]
    fn from(value: ConstCtOption<T>) -> Self {
        CtOption::new(value.value, value.is_some.into())
    }
}

impl<T> From<ConstCtOption<T>> for Option<T> {
    #[inline]
    fn from(value: ConstCtOption<T>) -> Self {
        if value.is_some.into() {
            Some(value.value)
        } else {
            None
        }
    }
}

// Need specific implementations to work around the
// "destructors cannot be evaluated at compile-time" error
// See https://github.com/rust-lang/rust/issues/66753

impl<const LIMBS: usize> ConstCtOption<Uint<LIMBS>> {
    /// This returns the underlying value if it is `Some` or the provided value otherwise.
    #[inline]
    pub const fn unwrap_or(self, def: Uint<LIMBS>) -> Uint<LIMBS> {
        Uint::select(&def, &self.value, self.is_some)
    }

    /// Returns the contained value, consuming the `self` value.
    ///
    /// # Panics
    ///
    /// Panics if the value is none with a custom panic message provided by
    /// `msg`.
    #[inline]
    #[track_caller]
    pub const fn expect(self, msg: &str) -> Uint<LIMBS> {
        assert!(self.is_some.to_bool_vartime(), "{}", msg);
        self.value
    }

    /// Returns the contained value, interpreting the underlying [`Uint`] value as an [`Int`].
    #[inline]
    pub const fn as_int(&self) -> ConstCtOption<Int<LIMBS>> {
        ConstCtOption::new(*self.value.as_int(), self.is_some)
    }
}

impl<const LIMBS: usize> ConstCtOption<(Uint<LIMBS>, Uint<LIMBS>)> {
    /// Returns the contained value, consuming the `self` value.
    ///
    /// # Panics
    ///
    /// Panics if the value is none with a custom panic message provided by
    /// `msg`.
    #[inline]
    #[track_caller]
    pub const fn expect(self, msg: &str) -> (Uint<LIMBS>, Uint<LIMBS>) {
        assert!(self.is_some.to_bool_vartime(), "{}", msg);
        self.value
    }
}

impl<const LIMBS: usize> ConstCtOption<NonZero<Uint<LIMBS>>> {
    /// Returns the contained value, consuming the `self` value.
    ///
    /// # Panics
    ///
    /// Panics if the value is none with a custom panic message provided by
    /// `msg`.
    #[inline]
    #[track_caller]
    pub const fn expect(self, msg: &str) -> NonZero<Uint<LIMBS>> {
        assert!(self.is_some.to_bool_vartime(), "{}", msg);
        self.value
    }
}

impl<const LIMBS: usize> ConstCtOption<Odd<Uint<LIMBS>>> {
    /// Returns the contained value, consuming the `self` value.
    ///
    /// # Panics
    ///
    /// Panics if the value is none with a custom panic message provided by
    /// `msg`.
    #[inline]
    #[track_caller]
    pub const fn expect(self, msg: &str) -> Odd<Uint<LIMBS>> {
        assert!(self.is_some.to_bool_vartime(), "{}", msg);
        self.value
    }
}

impl<const LIMBS: usize> ConstCtOption<Int<LIMBS>> {
    /// This returns the underlying value if it is `Some` or the provided value otherwise.
    #[inline]
    pub const fn unwrap_or(self, def: Int<LIMBS>) -> Int<LIMBS> {
        Int::select(&def, &self.value, self.is_some)
    }

    /// Returns the contained value, consuming the `self` value.
    ///
    /// # Panics
    ///
    /// Panics if the value is none with a custom panic message provided by
    /// `msg`.
    #[inline]
    #[track_caller]
    pub const fn expect(self, msg: &str) -> Int<LIMBS> {
        assert!(self.is_some.to_bool_vartime(), "{}", msg);
        self.value
    }
}

impl<const LIMBS: usize> ConstCtOption<NonZeroInt<LIMBS>> {
    /// Returns the contained value, consuming the `self` value.
    ///
    /// # Panics
    ///
    /// Panics if the value is none with a custom panic message provided by
    /// `msg`.
    #[inline]
    #[track_caller]
    pub const fn expect(self, msg: &str) -> NonZeroInt<LIMBS> {
        assert!(self.is_some.to_bool_vartime(), "{}", msg);
        self.value
    }
}

impl<const LIMBS: usize> ConstCtOption<OddInt<LIMBS>> {
    /// Returns the contained value, consuming the `self` value.
    ///
    /// # Panics
    ///
    /// Panics if the value is none with a custom panic message provided by
    /// `msg`.
    #[inline]
    #[track_caller]
    pub const fn expect(self, msg: &str) -> OddInt<LIMBS> {
        assert!(self.is_some.to_bool_vartime(), "{}", msg);
        self.value
    }
}

impl ConstCtOption<NonZero<Limb>> {
    /// Returns the contained value, consuming the `self` value.
    ///
    /// # Panics
    ///
    /// Panics if the value is none with a custom panic message provided by
    /// `msg`.
    #[inline]
    #[track_caller]
    pub const fn expect(self, msg: &str) -> NonZero<Limb> {
        assert!(self.is_some.to_bool_vartime(), "{}", msg);
        self.value
    }
}

impl<const LIMBS: usize> ConstCtOption<SafeGcdInverter<LIMBS>> {
    /// Returns the contained value, consuming the `self` value.
    ///
    /// # Panics
    ///
    /// Panics if the value is none with a custom panic message provided by
    /// `msg`.
    #[inline]
    #[track_caller]
    pub const fn expect(self, msg: &str) -> SafeGcdInverter<LIMBS> {
        assert!(self.is_some.to_bool_vartime(), "{}", msg);
        self.value
    }
}

impl<MOD: ConstMontyParams<LIMBS>, const LIMBS: usize> ConstCtOption<ConstMontyForm<MOD, LIMBS>> {
    /// This returns the underlying value if it is `Some` or the provided value otherwise.
    #[inline]
    pub const fn unwrap_or(self, def: ConstMontyForm<MOD, LIMBS>) -> ConstMontyForm<MOD, LIMBS> {
        ConstMontyForm::<MOD, LIMBS>::select(&def, &self.value, self.is_some)
    }

    /// Returns the contained value, consuming the `self` value.
    ///
    /// # Panics
    ///
    /// Panics if the value is none with a custom panic message provided by `msg`.
    #[inline]
    #[track_caller]
    pub const fn expect(self, msg: &str) -> ConstMontyForm<MOD, LIMBS> {
        assert!(self.is_some.to_bool_vartime(), "{}", msg);
        self.value
    }
}

#[cfg(test)]
mod tests {
    use super::{u32_max, u32_min};

    #[test]
    fn test_u32_const_min() {
        assert_eq!(u32_min(0, 5), 0);
        assert_eq!(u32_min(7, 0), 0);
        assert_eq!(u32_min(7, 5), 5);
        assert_eq!(u32_min(7, 7), 7);
    }

    #[test]
    fn test_u32_const_max() {
        assert_eq!(u32_max(0, 5), 5);
        assert_eq!(u32_max(7, 0), 7);
        assert_eq!(u32_max(7, 5), 7);
        assert_eq!(u32_max(7, 7), 7);
    }
}
