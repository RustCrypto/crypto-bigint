//! Shared encoding support.

use core::fmt;

#[cfg(feature = "hybrid-array")]
use {
    crate::Integer,
    core::ops::Add,
    hybrid_array::{Array, ArraySize, typenum::Unsigned},
};

/// Byte order used when encoding/decoding field elements as bytestrings.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ByteOrder {
    /// Big endian.
    BigEndian,

    /// Little endian.
    LittleEndian,
}

/// Alias for a byte array whose size is defined by [`ArrayEncoding::ByteSize`].
#[cfg(feature = "hybrid-array")]
pub type ByteArray<T> = Array<u8, <T as ArrayEncoding>::ByteSize>;

/// Support for encoding a big integer as a `Array`.
#[cfg(feature = "hybrid-array")]
pub trait ArrayEncoding: Encoding {
    /// Size of a byte array which encodes a big integer.
    type ByteSize: ArraySize + Add + Eq + Ord + Unsigned;

    /// Deserialize from a big-endian byte array.
    fn from_be_byte_array(bytes: ByteArray<Self>) -> Self;

    /// Deserialize from a little-endian byte array.
    fn from_le_byte_array(bytes: ByteArray<Self>) -> Self;

    /// Serialize to a big-endian byte array.
    fn to_be_byte_array(&self) -> ByteArray<Self>;

    /// Serialize to a little-endian byte array.
    fn to_le_byte_array(&self) -> ByteArray<Self>;
}

/// Support for decoding a `Array` as a big integer.
#[cfg(feature = "hybrid-array")]
pub trait ArrayDecoding {
    /// Big integer which decodes a `Array`.
    type Output: ArrayEncoding + Integer;

    /// Deserialize from a big-endian `Array`.
    fn into_uint_be(self) -> Self::Output;

    /// Deserialize from a little-endian `Array`.
    fn into_uint_le(self) -> Self::Output;
}

/// Encoding support.
pub trait Encoding: Sized {
    /// Byte array representation.
    type Repr: AsRef<[u8]>
        + AsMut<[u8]>
        + Clone
        + Sized
        + for<'a> TryFrom<&'a [u8], Error: core::error::Error>;

    /// Decode from big endian bytes.
    #[must_use]
    fn from_be_bytes(bytes: Self::Repr) -> Self;

    /// Decode from little endian bytes.
    #[must_use]
    fn from_le_bytes(bytes: Self::Repr) -> Self;

    /// Decode from bytes using the specified [`ByteOrder`].
    #[must_use]
    fn from_bytes(bytes: Self::Repr, byte_order: ByteOrder) -> Self {
        match byte_order {
            ByteOrder::BigEndian => Self::from_be_bytes(bytes),
            ByteOrder::LittleEndian => Self::from_le_bytes(bytes),
        }
    }

    /// Encode to big endian bytes.
    #[must_use]
    fn to_be_bytes(&self) -> Self::Repr;

    /// Encode to little endian bytes.
    #[must_use]
    fn to_le_bytes(&self) -> Self::Repr;

    /// Encode to bytes using the specified [`ByteOrder`].
    #[must_use]
    fn to_bytes(&self, byte_order: ByteOrder) -> Self::Repr {
        match byte_order {
            ByteOrder::BigEndian => self.to_be_bytes(),
            ByteOrder::LittleEndian => self.to_le_bytes(),
        }
    }
}

/// A trait mapping between encoded representations of integers.
pub trait EncodedSize {
    /// The equivalent encoded representation.
    type Target;
}

/// Possible errors in variable-time integer decoding methods.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum DecodeError {
    /// The input value was empty.
    Empty,

    /// The input was not consistent with the format restrictions.
    InvalidDigit,

    /// Input size is too small to fit in the given precision.
    InputSize,

    /// The deserialized number is larger than the given precision.
    Precision,
}

impl fmt::Display for DecodeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Empty => write!(f, "empty value provided"),
            Self::InvalidDigit => {
                write!(f, "invalid digit character")
            }
            Self::InputSize => write!(f, "input size is too small to fit in the given precision"),
            Self::Precision => write!(
                f,
                "the deserialized number is larger than the given precision"
            ),
        }
    }
}

impl core::error::Error for DecodeError {}
