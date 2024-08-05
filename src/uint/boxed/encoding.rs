//! Const-friendly decoding operations for [`BoxedUint`].

use super::BoxedUint;
use crate::{uint::encoding, DecodeError, Limb, Word};
use alloc::{boxed::Box, vec::Vec};
use subtle::{Choice, CtOption};

impl BoxedUint {
    /// Create a new [`BoxedUint`] from the provided big endian bytes.
    ///
    /// The `bits_precision` argument represents the precision of the resulting integer, which is
    /// fixed as this type is not arbitrary-precision.
    /// The new [`BoxedUint`] will be created with `bits_precision`
    /// rounded up to a multiple of [`Limb::BITS`].
    ///
    /// If the length of `bytes` is larger than `bits_precision` (rounded up to a multiple of 8)
    /// this function will return [`DecodeError::InputSize`].
    /// If the size of the decoded integer is larger than `bits_precision`,
    /// this function will return [`DecodeError::Precision`].
    pub fn from_be_slice(bytes: &[u8], bits_precision: u32) -> Result<Self, DecodeError> {
        if bytes.is_empty() && bits_precision == 0 {
            return Ok(Self::zero());
        }

        if bytes.len() > (bits_precision as usize + 7) / 8 {
            return Err(DecodeError::InputSize);
        }

        let mut ret = Self::zero_with_precision(bits_precision);

        for (chunk, limb) in bytes.rchunks(Limb::BYTES).zip(ret.limbs.iter_mut()) {
            *limb = Limb::from_be_slice(chunk);
        }

        if bits_precision < ret.bits() {
            return Err(DecodeError::Precision);
        }

        Ok(ret)
    }

    /// Create a new [`BoxedUint`] from the provided little endian bytes.
    ///
    /// The `bits_precision` argument represents the precision of the resulting integer, which is
    /// fixed as this type is not arbitrary-precision.
    /// The new [`BoxedUint`] will be created with `bits_precision`
    /// rounded up to a multiple of [`Limb::BITS`].
    ///
    /// If the length of `bytes` is larger than `bits_precision` (rounded up to a multiple of 8)
    /// this function will return [`DecodeError::InputSize`].
    /// If the size of the decoded integer is larger than `bits_precision`,
    /// this function will return [`DecodeError::Precision`].
    pub fn from_le_slice(bytes: &[u8], bits_precision: u32) -> Result<Self, DecodeError> {
        if bytes.is_empty() && bits_precision == 0 {
            return Ok(Self::zero());
        }

        if bytes.len() > (bits_precision as usize + 7) / 8 {
            return Err(DecodeError::InputSize);
        }

        let mut ret = Self::zero_with_precision(bits_precision);

        for (chunk, limb) in bytes.chunks(Limb::BYTES).zip(ret.limbs.iter_mut()) {
            *limb = Limb::from_le_slice(chunk);
        }

        if bits_precision < ret.bits() {
            return Err(DecodeError::Precision);
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

    /// Create a new [`BoxedUint`] from the provided big endian hex string.
    pub fn from_be_hex(hex: &str, bits_precision: u32) -> CtOption<Self> {
        let nlimbs = (bits_precision / Limb::BITS) as usize;
        let bytes = hex.as_bytes();

        assert!(
            bytes.len() == Limb::BYTES * nlimbs * 2,
            "hex string is not the expected size"
        );
        let mut res = vec![Limb::ZERO; nlimbs];
        let mut buf = [0u8; Limb::BYTES];
        let mut i = 0;
        let mut err = 0;

        while i < nlimbs {
            let mut j = 0;
            while j < Limb::BYTES {
                let offset = (i * Limb::BYTES + j) * 2;
                let (result, byte_err) =
                    encoding::decode_hex_byte([bytes[offset], bytes[offset + 1]]);
                err |= byte_err;
                buf[j] = result;
                j += 1;
            }
            res[nlimbs - i - 1] = Limb(Word::from_be_bytes(buf));
            i += 1;
        }
        CtOption::new(Self { limbs: res.into() }, Choice::from((err == 0) as u8))
    }

    /// Create a new [`BoxedUint`] from a big-endian string in a given base.
    ///
    /// The string may begin with a `+` character, and may use underscore
    /// characters to separate digits.
    ///
    /// If the input value contains non-digit characters or digits outside of the range `0..radix`
    /// this function will return [`DecodeError::InvalidDigit`].
    /// Panics if `radix` is not in the range from 2 to 36.
    pub fn from_str_radix_vartime(src: &str, radix: u32) -> Result<Self, DecodeError> {
        let mut dec = VecDecodeByLimb::default();
        encoding::decode_str_radix(src, radix, &mut dec)?;
        Ok(Self {
            limbs: dec.limbs.into(),
        })
    }

    /// Create a new [`BoxedUint`] from a big-endian string in a given base,
    /// with a given precision.
    ///
    /// The string may begin with a `+` character, and may use underscore
    /// characters to separate digits.
    ///
    /// The `bits_precision` argument represents the precision of the resulting integer, which is
    /// fixed as this type is not arbitrary-precision.
    /// The new [`BoxedUint`] will be created with `bits_precision` rounded up to a multiple
    /// of [`Limb::BITS`].
    ///
    /// If the input value contains non-digit characters or digits outside of the range `0..radix`
    /// this function will return [`DecodeError::InvalidDigit`].
    /// If the length of `bytes` is larger than `bits_precision` (rounded up to a multiple of 8)
    /// this function will return [`DecodeError::InputSize`].
    /// If the size of the decoded integer is larger than `bits_precision`,
    /// this function will return [`DecodeError::Precision`].
    /// Panics if `radix` is not in the range from 2 to 36.
    pub fn from_str_radix_with_precision_vartime(
        src: &str,
        radix: u32,
        bits_precision: u32,
    ) -> Result<Self, DecodeError> {
        let mut ret = Self::zero_with_precision(bits_precision);
        encoding::decode_str_radix(
            src,
            radix,
            &mut encoding::SliceDecodeByLimb::new(&mut ret.limbs),
        )?;
        if bits_precision < ret.bits() {
            return Err(DecodeError::Precision);
        }
        Ok(ret)
    }
}

/// Decoder target producing a Vec<Limb>
#[derive(Default)]
struct VecDecodeByLimb {
    limbs: Vec<Limb>,
}

impl encoding::DecodeByLimb for VecDecodeByLimb {
    #[inline]
    fn limbs_mut(&mut self) -> &mut [Limb] {
        self.limbs.as_mut_slice()
    }

    #[inline]
    fn push_limb(&mut self, limb: Limb) -> bool {
        self.limbs.push(limb);
        true
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
    #[cfg(target_pointer_width = "64")]
    fn from_be_hex_eq() {
        let hex = "00112233445566778899aabbccddeeff";
        let n = BoxedUint::from_be_hex(hex, 128).unwrap();
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
    #[cfg(target_pointer_width = "32")]
    fn from_be_slice_not_word_sized() {
        let bytes = hex!("112233445566778899aabbccddeeff");
        let n = BoxedUint::from_be_slice(&bytes, 127).unwrap();
        assert_eq!(
            n.as_limbs(),
            &[
                Limb(0xccddeeff),
                Limb(0x8899aabb),
                Limb(0x44556677),
                Limb(0x00112233)
            ]
        );
        assert_eq!(n.bits_precision(), 128);
    }

    #[test]
    #[cfg(target_pointer_width = "64")]
    fn from_be_slice_not_word_sized() {
        let bytes = hex!("112233445566778899aabbccddeeff");
        let n = BoxedUint::from_be_slice(&bytes, 127).unwrap();
        assert_eq!(
            n.as_limbs(),
            &[Limb(0x8899aabbccddeeff), Limb(0x0011223344556677)]
        );
        assert_eq!(n.bits_precision(), 128);
    }

    #[test]
    fn from_be_slice_non_multiple_precision() {
        let bytes = hex!("0f112233445566778899aabbccddeeff");
        assert_eq!(
            BoxedUint::from_be_slice(&bytes, 121),
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
    #[cfg(target_pointer_width = "32")]
    fn from_le_slice_not_word_sized() {
        let bytes = hex!("ffeeddccbbaa998877665544332211");
        let n = BoxedUint::from_le_slice(&bytes, 127).unwrap();
        assert_eq!(
            n.as_limbs(),
            &[
                Limb(0xccddeeff),
                Limb(0x8899aabb),
                Limb(0x44556677),
                Limb(0x00112233)
            ]
        );
        assert_eq!(n.bits_precision(), 128);
    }

    #[test]
    #[cfg(target_pointer_width = "64")]
    fn from_le_slice_not_word_sized() {
        let bytes = hex!("ffeeddccbbaa998877665544332211");
        let n = BoxedUint::from_le_slice(&bytes, 127).unwrap();
        assert_eq!(
            n.as_limbs(),
            &[Limb(0x8899aabbccddeeff), Limb(0x0011223344556677)]
        );
        assert_eq!(n.bits_precision(), 128);
    }

    #[test]
    fn from_le_slice_non_multiple_precision() {
        let bytes = hex!("ffeeddccbbaa998877665544332211f0");
        assert_eq!(
            BoxedUint::from_le_slice(&bytes, 121),
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

    #[test]
    fn from_str_radix_invalid() {
        assert_eq!(
            BoxedUint::from_str_radix_vartime("?", 10,),
            Err(DecodeError::InvalidDigit)
        );
        assert_eq!(
            BoxedUint::from_str_radix_with_precision_vartime(
                "ffffffffffffffff_ffffffffffffffff_f",
                16,
                128
            ),
            Err(DecodeError::InputSize)
        );
        assert_eq!(
            BoxedUint::from_str_radix_with_precision_vartime("1111111111111111", 2, 10),
            Err(DecodeError::Precision)
        );
    }

    #[test]
    fn from_str_radix_10() {
        let dec = "+340_282_366_920_938_463_463_374_607_431_768_211_455";
        let res = BoxedUint::from_str_radix_vartime(dec, 10).expect("error decoding");
        assert_eq!(res, BoxedUint::max(128));
    }

    #[test]
    fn from_str_radix_16() {
        let hex = "fedcba9876543210fedcba9876543210";
        let res = BoxedUint::from_str_radix_vartime(hex, 16).expect("error decoding");
        assert_eq!(hex, format!("{res:x}"));
    }
}
