//! Limb encoding

use super::{Limb, Word};
use crate::Encoding;

impl Encoding for Limb {
    type Repr = [u8; Self::BYTES];

    #[inline]
    fn from_be_bytes(bytes: Self::Repr) -> Self {
        Limb(Word::from_be_bytes(bytes))
    }

    #[inline]
    fn from_le_bytes(bytes: Self::Repr) -> Self {
        Limb(Word::from_le_bytes(bytes))
    }

    #[inline]
    fn to_be_bytes(&self) -> Self::Repr {
        self.0.to_be_bytes()
    }

    #[inline]
    fn to_le_bytes(&self) -> Self::Repr {
        self.0.to_le_bytes()
    }
}

#[cfg(feature = "alloc")]
impl Limb {
    /// Decode limb from a big endian byte slice, which may be shorter than [`Limb::BYTES`].
    ///
    /// # Panics
    /// - if the slice is larger than [`Limb::Repr`].
    pub(crate) fn from_be_slice(bytes: &[u8]) -> Self {
        let offset = Limb::BYTES
            .checked_sub(bytes.len())
            .expect("The given slice is larger than Limb::BYTES");

        let mut repr = Self::ZERO.to_be_bytes();
        repr[offset..].copy_from_slice(bytes);
        Self::from_be_bytes(repr)
    }

    /// Decode limb from a little endian byte slice, which may be shorter than [`Limb::BYTES`].
    ///
    /// # Panics
    /// - if the slice is not the same size as [`Limb::Repr`].
    pub(crate) fn from_le_slice(bytes: &[u8]) -> Self {
        assert!(
            bytes.len() <= Limb::BYTES,
            "The given slice is larger than Limb::BYTES"
        );

        let mut repr = Self::ZERO.to_be_bytes();
        repr[..bytes.len()].copy_from_slice(bytes);
        Self::from_le_bytes(repr)
    }
}

#[cfg(test)]
mod test {
    use super::*;

    cpubits::cpubits! {
        32 => { const LIMB: Limb = Limb(0x7654_3210); }
        64 => { const LIMB: Limb = Limb(0xFEDCBA9876543210); }
    }

    #[test]
    fn roundtrip() {
        assert_eq!(LIMB, Limb::from_be_bytes(LIMB.to_be_bytes()));
        assert_eq!(LIMB, Limb::from_le_bytes(LIMB.to_le_bytes()));
    }

    #[test]
    fn reverse() {
        let mut bytes = LIMB.to_be_bytes();
        bytes.reverse();
        assert_eq!(LIMB, Limb::from_le_bytes(bytes));

        let mut bytes = LIMB.to_le_bytes();
        bytes.reverse();
        assert_eq!(LIMB, Limb::from_be_bytes(bytes));
    }
}
