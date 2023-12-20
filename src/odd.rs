//! Wrapper type for non-zero integers.

use crate::{Integer, NonZero};
use core::ops::Deref;
use subtle::{Choice, ConditionallySelectable, CtOption};

/// Wrapper type for odd integers.
///
/// These are frequently used in cryptography, e.g. as a modulus.
#[derive(Clone, Copy, Debug, Default, Eq, Hash, PartialEq, PartialOrd, Ord)]
#[repr(transparent)]
pub struct Odd<T>(pub(crate) T);

impl<T> Odd<T> {
    /// Create a new odd integer.
    pub fn new(n: T) -> CtOption<Self>
    where
        T: Integer,
    {
        let is_odd = n.is_odd();
        CtOption::new(Self(n), is_odd)
    }

    /// Provides access to the contents of [`Odd`] in a `const` context.
    pub const fn as_ref(&self) -> &T {
        &self.0
    }

    /// All odd integers are definitionally non-zero, so we can also obtain a reference to [`NonZero`].
    pub const fn as_nz_ref(&self) -> &NonZero<T> {
        #[allow(trivial_casts, unsafe_code)]
        unsafe {
            &*(&self.0 as *const T as *const NonZero<T>)
        }
    }

    /// Returns the inner value.
    pub fn get(self) -> T {
        self.0
    }
}

impl<T> AsRef<T> for Odd<T> {
    fn as_ref(&self) -> &T {
        &self.0
    }
}

impl<T> AsRef<NonZero<T>> for Odd<T> {
    fn as_ref(&self) -> &NonZero<T> {
        self.as_nz_ref()
    }
}

impl<T> ConditionallySelectable for Odd<T>
where
    T: ConditionallySelectable,
{
    fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
        Self(T::conditional_select(&a.0, &b.0, choice))
    }
}

impl<T> Deref for Odd<T> {
    type Target = T;

    fn deref(&self) -> &T {
        &self.0
    }
}
