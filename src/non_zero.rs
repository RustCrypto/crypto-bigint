//! Wrapper type for non-zero integers.

#[cfg(feature = "rand")]
use crate::Random;
use crate::{Encoding, Integer, UInt};
use core::{
    fmt,
    num::{NonZeroU128, NonZeroU16, NonZeroU32, NonZeroU64, NonZeroU8},
    ops::Deref,
};
use subtle::{Choice, ConditionallySelectable, ConstantTimeEq, CtOption};

#[cfg(feature = "generic-array")]
use crate::{ArrayEncoding, ByteArray};

#[cfg(feature = "rand")]
use rand_core::{CryptoRng, RngCore};

/// Wrapper type for non-zero integers.
#[derive(Copy, Clone, Default, Eq, PartialEq, PartialOrd, Ord)]
pub struct NonZero<T: Integer>(T);

impl<T> NonZero<T>
where
    T: Integer,
{
    /// The value `1`.
    pub const ONE: Self = Self(T::ONE);

    /// Maximum value this integer can express.
    pub const MAX: Self = Self(T::MAX);

    /// Create a new non-zero integer.
    pub fn new(n: T) -> CtOption<Self> {
        CtOption::new(Self(n), !n.is_zero())
    }

    /// Decode from big endian bytes.
    pub fn from_be_bytes(bytes: T::Repr) -> CtOption<Self>
    where
        T: Encoding,
    {
        Self::new(T::from_be_bytes(bytes))
    }

    /// Decode from little endian bytes.
    pub fn from_le_bytes(bytes: T::Repr) -> CtOption<Self>
    where
        T: Encoding,
    {
        Self::new(T::from_le_bytes(bytes))
    }

    /// Decode a non-zero integer from big endian bytes.
    #[cfg(feature = "generic-array")]
    pub fn from_be_byte_array(bytes: ByteArray<T>) -> CtOption<Self>
    where
        T: ArrayEncoding,
    {
        Self::new(T::from_be_byte_array(bytes))
    }

    /// Decode a non-zero integer from big endian bytes.
    #[cfg(feature = "generic-array")]
    pub fn from_le_byte_array(bytes: ByteArray<T>) -> CtOption<Self>
    where
        T: ArrayEncoding,
    {
        Self::new(T::from_be_byte_array(bytes))
    }
}

impl<const LIMBS: usize> NonZero<UInt<LIMBS>>
where
    UInt<LIMBS>: Integer,
{
    /// Create a [`NonZero<UInt>`] from a [`NonZeroU8`] (const-friendly)
    // TODO(tarcieri): replace with `const impl From<NonZeroU8>` when stable
    pub const fn from_u8(n: NonZeroU8) -> Self {
        Self(UInt::from_u8(n.get()))
    }

    /// Create a [`NonZero<UInt>`] from a [`NonZeroU16`] (const-friendly)
    // TODO(tarcieri): replace with `const impl From<NonZeroU16>` when stable
    pub const fn from_u16(n: NonZeroU16) -> Self {
        Self(UInt::from_u16(n.get()))
    }

    /// Create a [`NonZero<UInt>`] from a [`NonZeroU32`] (const-friendly)
    // TODO(tarcieri): replace with `const impl From<NonZeroU32>` when stable
    pub const fn from_u32(n: NonZeroU32) -> Self {
        Self(UInt::from_u32(n.get()))
    }

    /// Create a [`NonZero<UInt>`] from a [`NonZeroU64`] (const-friendly)
    // TODO(tarcieri): replace with `const impl From<NonZeroU64>` when stable
    pub const fn from_u64(n: NonZeroU64) -> Self {
        Self(UInt::from_u64(n.get()))
    }

    /// Create a [`NonZero<UInt>`] from a [`NonZeroU128`] (const-friendly)
    // TODO(tarcieri): replace with `const impl From<NonZeroU128>` when stable
    pub const fn from_u128(n: NonZeroU128) -> Self {
        Self(UInt::from_u128(n.get()))
    }
}

impl<T> AsRef<T> for NonZero<T>
where
    T: Integer,
{
    fn as_ref(&self) -> &T {
        &self.0
    }
}

impl<T> ConditionallySelectable for NonZero<T>
where
    T: Integer,
{
    fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
        Self(T::conditional_select(&a.0, &b.0, choice))
    }
}

impl<T> ConstantTimeEq for NonZero<T>
where
    T: Integer,
{
    fn ct_eq(&self, other: &Self) -> Choice {
        self.0.ct_eq(&other.0)
    }
}

impl<T> Deref for NonZero<T>
where
    T: Integer,
{
    type Target = T;

    fn deref(&self) -> &T {
        &self.0
    }
}

#[cfg(feature = "rand")]
#[cfg_attr(docsrs, doc(cfg(feature = "rand")))]
impl<T> Random for NonZero<T>
where
    T: Integer + Random,
{
    /// Generate a random `NonZero<T>`.
    fn random(mut rng: impl CryptoRng + RngCore) -> Self {
        // Use rejection sampling to eliminate zero values.
        // While this method isn't constant-time, the attacker shouldn't learn
        // anything about unrelated outputs so long as `rng` is a secure `CryptoRng`.
        loop {
            if let Some(result) = Self::new(T::random(&mut rng)).into() {
                break result;
            }
        }
    }
}

impl<T> fmt::Display for NonZero<T>
where
    T: Integer + fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(&self.0, f)
    }
}

impl<T> fmt::Binary for NonZero<T>
where
    T: Integer + fmt::Binary,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Binary::fmt(&self.0, f)
    }
}

impl<T> fmt::Octal for NonZero<T>
where
    T: Integer + fmt::Octal,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Octal::fmt(&self.0, f)
    }
}

impl<T> fmt::LowerHex for NonZero<T>
where
    T: Integer + fmt::LowerHex,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::LowerHex::fmt(&self.0, f)
    }
}

impl<T> fmt::UpperHex for NonZero<T>
where
    T: Integer + fmt::UpperHex,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::UpperHex::fmt(&self.0, f)
    }
}

impl<const LIMBS: usize> From<NonZeroU8> for NonZero<UInt<LIMBS>>
where
    UInt<LIMBS>: Integer,
{
    fn from(integer: NonZeroU8) -> Self {
        Self::from_u8(integer)
    }
}

impl<const LIMBS: usize> From<NonZeroU16> for NonZero<UInt<LIMBS>>
where
    UInt<LIMBS>: Integer,
{
    fn from(integer: NonZeroU16) -> Self {
        Self::from_u16(integer)
    }
}

impl<const LIMBS: usize> From<NonZeroU32> for NonZero<UInt<LIMBS>>
where
    UInt<LIMBS>: Integer,
{
    fn from(integer: NonZeroU32) -> Self {
        Self::from_u32(integer)
    }
}

impl<const LIMBS: usize> From<NonZeroU64> for NonZero<UInt<LIMBS>>
where
    UInt<LIMBS>: Integer,
{
    fn from(integer: NonZeroU64) -> Self {
        Self::from_u64(integer)
    }
}

impl<const LIMBS: usize> From<NonZeroU128> for NonZero<UInt<LIMBS>>
where
    UInt<LIMBS>: Integer,
{
    fn from(integer: NonZeroU128) -> Self {
        Self::from_u128(integer)
    }
}
