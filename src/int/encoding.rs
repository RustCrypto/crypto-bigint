//! Const-friendly decoding/encoding operations for [`Int`].

use crate::{Int, Uint};

impl<const LIMBS: usize> Int<LIMBS> {
    /// Create a new [`Int`] from the provided big endian bytes.
    ///
    /// See [`Uint::from_be_slice`] for more details.
    pub const fn from_be_slice(bytes: &[u8]) -> Self {
        Self(Uint::from_be_slice(bytes))
    }

    /// Create a new [`Int`] from the provided big endian hex string.
    ///
    /// Panics if the hex is malformed or not zero-padded accordingly for the size.
    ///
    /// See [`Uint::from_be_hex`] for more details.
    pub const fn from_be_hex(hex: &str) -> Self {
        Self(Uint::from_be_hex(hex))
    }

    /// Create a new [`Int`] from the provided little endian bytes.
    ///
    /// See [`Uint::from_le_slice`] for more details.
    pub const fn from_le_slice(bytes: &[u8]) -> Self {
        Self(Uint::from_le_slice(bytes))
    }

    /// Create a new [`Int`] from the provided little endian hex string.
    ///
    /// Panics if the hex is malformed or not zero-padded accordingly for the size.
    ///
    /// See [`Uint::from_le_hex`] for more details.
    pub const fn from_le_hex(hex: &str) -> Self {
        Self(Uint::from_le_hex(hex))
    }
}

/// Encode an [`Int`] to a big endian byte array of the given size.
pub(crate) const fn int_to_be_bytes<const LIMBS: usize, const BYTES: usize>(
    int: &Int<LIMBS>,
) -> [u8; BYTES] {
    crate::uint::encoding::uint_to_be_bytes(&int.0)
}

/// Encode an [`Int`] to a little endian byte array of the given size.
pub(crate) const fn int_to_le_bytes<const LIMBS: usize, const BYTES: usize>(
    int: &Int<LIMBS>,
) -> [u8; BYTES] {
    crate::uint::encoding::uint_to_le_bytes(&int.0)
}
