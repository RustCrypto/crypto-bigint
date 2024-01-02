//! Wrapper type for non-zero integers.

use crate::{Integer, Limb, NonZero, Uint};
use core::{cmp::Ordering, ops::Deref};
use subtle::{Choice, ConditionallySelectable, CtOption};

#[cfg(feature = "alloc")]
use crate::BoxedUint;

#[cfg(feature = "rand_core")]
use {crate::Random, rand_core::CryptoRngCore};

#[cfg(all(feature = "alloc", feature = "rand_core"))]
use crate::RandomBits;

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

impl<const LIMBS: usize> Odd<Uint<LIMBS>> {
    /// Create a new [`Odd<Uint<LIMBS>>`] from the provided big endian hex string.
    ///
    /// Panics if the hex is malformed or not zero-padded accordingly for the size, or if the value is even.
    pub const fn from_be_hex(hex: &str) -> Self {
        let uint = Uint::<LIMBS>::from_be_hex(hex);
        assert!(uint.is_odd().is_true_vartime(), "number must be odd");
        Odd(uint)
    }

    /// Create a new [`Odd<Uint<LIMBS>>`] from the provided little endian hex string.
    ///
    /// Panics if the hex is malformed or not zero-padded accordingly for the size, or if the value is even.
    pub const fn from_le_hex(hex: &str) -> Self {
        let uint = Uint::<LIMBS>::from_be_hex(hex);
        assert!(uint.is_odd().is_true_vartime(), "number must be odd");
        Odd(uint)
    }
}

impl<T> AsRef<T> for Odd<T> {
    fn as_ref(&self) -> &T {
        &self.0
    }
}

impl<T> AsRef<[Limb]> for Odd<T>
where
    T: AsRef<[Limb]>,
{
    fn as_ref(&self) -> &[Limb] {
        self.0.as_ref()
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

impl<const LIMBS: usize> PartialEq<Odd<Uint<LIMBS>>> for Uint<LIMBS> {
    fn eq(&self, other: &Odd<Uint<LIMBS>>) -> bool {
        self.eq(&other.0)
    }
}

impl<const LIMBS: usize> PartialOrd<Odd<Uint<LIMBS>>> for Uint<LIMBS> {
    fn partial_cmp(&self, other: &Odd<Uint<LIMBS>>) -> Option<Ordering> {
        Some(self.cmp(&other.0))
    }
}

#[cfg(feature = "alloc")]
impl PartialEq<Odd<BoxedUint>> for BoxedUint {
    fn eq(&self, other: &Odd<BoxedUint>) -> bool {
        self.eq(&other.0)
    }
}

#[cfg(feature = "alloc")]
impl PartialOrd<Odd<BoxedUint>> for BoxedUint {
    fn partial_cmp(&self, other: &Odd<BoxedUint>) -> Option<Ordering> {
        Some(self.cmp(&other.0))
    }
}

#[cfg(feature = "rand_core")]
impl<const LIMBS: usize> Random for Odd<Uint<LIMBS>> {
    /// Generate a random `Odd<Uint<T>>`.
    fn random(rng: &mut impl CryptoRngCore) -> Self {
        let mut ret = Uint::random(rng);
        ret.limbs[0] |= Limb::ONE;
        Odd(ret)
    }
}

#[cfg(all(feature = "alloc", feature = "rand_core"))]
impl Odd<BoxedUint> {
    /// Generate a random `Odd<Uint<T>>`.
    pub fn random(rng: &mut impl CryptoRngCore, bit_length: u32) -> Self {
        let mut ret = BoxedUint::random_bits(rng, bit_length);
        ret.limbs[0] |= Limb::ONE;
        Odd(ret)
    }
}

#[cfg(test)]
mod tests {
    #[cfg(feature = "alloc")]
    use super::BoxedUint;
    use super::{Odd, Uint};

    #[test]
    fn not_odd_numbers() {
        let zero = Odd::new(Uint::<4>::ZERO);
        assert!(bool::from(zero.is_none()));
        let two = Odd::new(Uint::<4>::from(2u8));
        assert!(bool::from(two.is_none()));
    }

    #[cfg(feature = "alloc")]
    #[test]
    fn not_odd_numbers_boxed() {
        let zero = Odd::new(BoxedUint::zero());
        assert!(bool::from(zero.is_none()));
        let two = Odd::new(BoxedUint::from(2u8));
        assert!(bool::from(two.is_none()));
    }
}
