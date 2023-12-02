//! Const-friendly decoding operations for [`BoxedUint`].

use super::BoxedUint;
use crate::Limb;
use alloc::boxed::Box;
use core::fmt;

/// Decoding errors for [`BoxedUint`].
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum DecodeError {
    /// Input is not a valid size.
    InputSize,

    /// Precision is not a multiple of [`Limb::BYTES`].
    Precision,
}

impl fmt::Display for DecodeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InputSize => write!(f, "input is not a valid size"),
            Self::Precision => write!(f, "precision is not a multiple of the word size"),
        }
    }
}

#[cfg(feature = "std")]
impl std::error::Error for DecodeError {}

impl BoxedUint {
    /// Create a new [`BoxedUint`] from the provided big endian bytes.
    ///
    /// The `bits_precision` argument represents the precision of the resulting integer, which is
    /// fixed as this type is not arbitrary-precision. It MUST be a multiple of the limb size, i.e.
    /// [`Limb::BITS`], or otherwise this function will return [`DecodeError::Precision`].
    ///
    /// If the length of `bytes` (when interpreted as bits) is larger than `bits_precision`, this
    /// function will return [`DecodeError::InputSize`].
    pub fn from_be_slice(bytes: &[u8], bits_precision: usize) -> Result<Self, DecodeError> {
        if bytes.is_empty() && bits_precision == 0 {
            return Ok(Self::zero());
        }

        if bits_precision % Limb::BITS != 0 {
            return Err(DecodeError::Precision);
        }

        if bytes.len() % Limb::BYTES != 0 || bytes.len() * 8 > bits_precision {
            return Err(DecodeError::InputSize);
        }

        let mut ret = Self::zero_with_precision(bits_precision);

        for (chunk, limb) in bytes.chunks(Limb::BYTES).rev().zip(ret.limbs.iter_mut()) {
            *limb = Limb::from_be_slice(chunk);
        }

        Ok(ret)
    }

    /// Create a new [`BoxedUint`] from the provided little endian bytes.
    ///
    /// The `bits_precision` argument represents the precision of the resulting integer, which is
    /// fixed as this type is not arbitrary-precision. It MUST be a multiple of the limb size, i.e.
    /// [`Limb::BITS`], or otherwise this function will return [`DecodeError::Precision`].
    ///
    /// If the length of `bytes` (when interpreted as bits) is larger than `bits_precision`, this
    /// function will return [`DecodeError::InputSize`].
    pub fn from_le_slice(bytes: &[u8], bits_precision: usize) -> Result<Self, DecodeError> {
        if bytes.is_empty() && bits_precision == 0 {
            return Ok(Self::zero());
        }

        if bits_precision % Limb::BITS != 0 {
            return Err(DecodeError::Precision);
        }

        if bytes.len() % Limb::BYTES != 0 || bytes.len() * 8 > bits_precision {
            return Err(DecodeError::InputSize);
        }

        let mut ret = Self::zero_with_precision(bits_precision);

        for (chunk, limb) in bytes.chunks(Limb::BYTES).zip(ret.limbs.iter_mut()) {
            *limb = Limb::from_le_slice(chunk);
        }

        Ok(ret)
    }

    /// Serialize this [`BoxedUint`] as big-endian.
    #[inline]
    pub fn to_be_bytes(&self) -> Box<[u8]> {
        let mut out = vec![0u8; self.limbs.len() * Limb::BYTES];

        for (src, dst) in self
            .limbs
            .iter()
            .rev()
            .cloned()
            .zip(out.chunks_exact_mut(Limb::BYTES))
        {
            dst.copy_from_slice(&src.0.to_be_bytes());
        }

        out.into()
    }

    /// Serialize this [`BoxedUint`] as little-endian.
    #[inline]
    pub fn to_le_bytes(&self) -> Box<[u8]> {
        let mut out = vec![0u8; self.limbs.len() * Limb::BYTES];

        for (src, dst) in self
            .limbs
            .iter()
            .cloned()
            .zip(out.chunks_exact_mut(Limb::BYTES))
        {
            dst.copy_from_slice(&src.0.to_le_bytes());
        }

        out.into()
    }
}

#[cfg(test)]
mod tests {
    use super::{BoxedUint, DecodeError};
    use crate::Limb;
    use hex_literal::hex;

    #[test]
    #[cfg(target_pointer_width = "32")]
    fn from_be_slice_eq() {
        let bytes = hex!("0011223344556677");
        let n = BoxedUint::from_be_slice(&bytes, 64).unwrap();
        assert_eq!(n.as_limbs(), &[Limb(0x44556677), Limb(0x00112233)]);
    }

    #[test]
    #[cfg(target_pointer_width = "64")]
    fn from_be_slice_eq() {
        let bytes = hex!("00112233445566778899aabbccddeeff");
        let n = BoxedUint::from_be_slice(&bytes, 128).unwrap();
        assert_eq!(
            n.as_limbs(),
            &[Limb(0x8899aabbccddeeff), Limb(0x0011223344556677)]
        );
    }

    #[test]
    #[cfg(target_pointer_width = "32")]
    fn from_be_slice_short() {
        let bytes = hex!("0011223344556677");
        let n = BoxedUint::from_be_slice(&bytes, 128).unwrap();
        assert_eq!(
            n.as_limbs(),
            &[Limb(0x44556677), Limb(0x00112233), Limb::ZERO, Limb::ZERO]
        );
    }

    #[test]
    #[cfg(target_pointer_width = "64")]
    fn from_be_slice_short() {
        let bytes = hex!("00112233445566778899aabbccddeeff");
        let n = BoxedUint::from_be_slice(&bytes, 256).unwrap();
        assert_eq!(
            n.as_limbs(),
            &[
                Limb(0x8899aabbccddeeff),
                Limb(0x0011223344556677),
                Limb::ZERO,
                Limb::ZERO
            ]
        );
    }

    #[test]
    fn from_be_slice_too_long() {
        let bytes = hex!("00112233445566778899aabbccddeeff");
        assert_eq!(
            BoxedUint::from_be_slice(&bytes, 64),
            Err(DecodeError::InputSize)
        );
    }

    #[test]
    fn from_be_slice_not_word_sized() {
        let bytes = hex!("00112233445566778899aabbccddee");
        assert_eq!(
            BoxedUint::from_be_slice(&bytes, 128),
            Err(DecodeError::InputSize)
        );
    }

    #[test]
    fn from_be_slice_bad_precision() {
        let bytes = hex!("00112233445566778899aabbccddeeff");
        assert_eq!(
            BoxedUint::from_be_slice(&bytes, 127),
            Err(DecodeError::Precision)
        );
    }

    #[test]
    #[cfg(target_pointer_width = "32")]
    fn from_le_slice_eq() {
        let bytes = hex!("7766554433221100");
        let n = BoxedUint::from_le_slice(&bytes, 64).unwrap();
        assert_eq!(n.as_limbs(), &[Limb(0x44556677), Limb(0x00112233)]);
    }

    #[test]
    #[cfg(target_pointer_width = "64")]
    fn from_le_slice_eq() {
        let bytes = hex!("ffeeddccbbaa99887766554433221100");
        let n = BoxedUint::from_le_slice(&bytes, 128).unwrap();
        assert_eq!(
            n.as_limbs(),
            &[Limb(0x8899aabbccddeeff), Limb(0x0011223344556677)]
        );
    }

    #[test]
    #[cfg(target_pointer_width = "32")]
    fn from_le_slice_short() {
        let bytes = hex!("7766554433221100");
        let n = BoxedUint::from_le_slice(&bytes, 128).unwrap();
        assert_eq!(
            n.as_limbs(),
            &[Limb(0x44556677), Limb(0x00112233), Limb::ZERO, Limb::ZERO]
        );
    }

    #[test]
    #[cfg(target_pointer_width = "64")]
    fn from_le_slice_short() {
        let bytes = hex!("ffeeddccbbaa99887766554433221100");
        let n = BoxedUint::from_le_slice(&bytes, 256).unwrap();
        assert_eq!(
            n.as_limbs(),
            &[
                Limb(0x8899aabbccddeeff),
                Limb(0x0011223344556677),
                Limb::ZERO,
                Limb::ZERO
            ]
        );
    }

    #[test]
    fn from_le_slice_too_long() {
        let bytes = hex!("ffeeddccbbaa99887766554433221100");
        assert_eq!(
            BoxedUint::from_be_slice(&bytes, 64),
            Err(DecodeError::InputSize)
        );
    }

    #[test]
    fn from_le_slice_not_word_sized() {
        let bytes = hex!("ffeeddccbbaa998877665544332211");
        assert_eq!(
            BoxedUint::from_be_slice(&bytes, 128),
            Err(DecodeError::InputSize)
        );
    }

    #[test]
    fn from_le_slice_bad_precision() {
        let bytes = hex!("ffeeddccbbaa99887766554433221100");
        assert_eq!(
            BoxedUint::from_le_slice(&bytes, 127),
            Err(DecodeError::Precision)
        );
    }

    #[test]
    fn to_be_bytes() {
        let bytes = hex!("00112233445566778899aabbccddeeff");
        let n = BoxedUint::from_be_slice(&bytes, 128).unwrap();
        assert_eq!(bytes.as_slice(), &*n.to_be_bytes());
    }

    #[test]
    fn to_le_bytes() {
        let bytes = hex!("ffeeddccbbaa99887766554433221100");
        let n = BoxedUint::from_be_slice(&bytes, 128).unwrap();
        assert_eq!(bytes.as_slice(), &*n.to_be_bytes());
    }
}
