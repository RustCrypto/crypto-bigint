//! Const-friendly decoding/encoding operations for [`Uint`].

#[cfg(all(feature = "der", feature = "hybrid-array"))]
mod der;

#[cfg(feature = "rlp")]
mod rlp;

use super::Uint;
use crate::{DecodeError, Limb, Word};

#[cfg(feature = "hybrid-array")]
use crate::Encoding;

impl<const LIMBS: usize> Uint<LIMBS> {
    /// Create a new [`Uint`] from the provided big endian bytes.
    pub const fn from_be_slice(bytes: &[u8]) -> Self {
        assert!(
            bytes.len() == Limb::BYTES * LIMBS,
            "bytes are not the expected size"
        );

        let mut res = [Limb::ZERO; LIMBS];
        let mut buf = [0u8; Limb::BYTES];
        let mut i = 0;

        while i < LIMBS {
            let mut j = 0;
            while j < Limb::BYTES {
                buf[j] = bytes[i * Limb::BYTES + j];
                j += 1;
            }
            res[LIMBS - i - 1] = Limb(Word::from_be_bytes(buf));
            i += 1;
        }

        Uint::new(res)
    }

    /// Create a new [`Uint`] from the provided big endian hex string.
    ///
    /// Panics if the hex is malformed or not zero-padded accordingly for the size.
    pub const fn from_be_hex(hex: &str) -> Self {
        let bytes = hex.as_bytes();

        assert!(
            bytes.len() == Limb::BYTES * LIMBS * 2,
            "hex string is not the expected size"
        );

        let mut res = [Limb::ZERO; LIMBS];
        let mut buf = [0u8; Limb::BYTES];
        let mut i = 0;
        let mut err = 0;

        while i < LIMBS {
            let mut j = 0;
            while j < Limb::BYTES {
                let offset = (i * Limb::BYTES + j) * 2;
                let (result, byte_err) = decode_hex_byte([bytes[offset], bytes[offset + 1]]);
                err |= byte_err;
                buf[j] = result;
                j += 1;
            }
            res[LIMBS - i - 1] = Limb(Word::from_be_bytes(buf));
            i += 1;
        }

        assert!(err == 0, "invalid hex byte");

        Uint::new(res)
    }

    /// Create a new [`Uint`] from the provided little endian bytes.
    pub const fn from_le_slice(bytes: &[u8]) -> Self {
        assert!(
            bytes.len() == Limb::BYTES * LIMBS,
            "bytes are not the expected size"
        );

        let mut res = [Limb::ZERO; LIMBS];
        let mut buf = [0u8; Limb::BYTES];
        let mut i = 0;

        while i < LIMBS {
            let mut j = 0;
            while j < Limb::BYTES {
                buf[j] = bytes[i * Limb::BYTES + j];
                j += 1;
            }
            res[i] = Limb(Word::from_le_bytes(buf));
            i += 1;
        }

        Uint::new(res)
    }

    /// Create a new [`Uint`] from the provided little endian hex string.
    ///
    /// Panics if the hex is malformed or not zero-padded accordingly for the size.
    pub const fn from_le_hex(hex: &str) -> Self {
        let bytes = hex.as_bytes();

        assert!(
            bytes.len() == Limb::BYTES * LIMBS * 2,
            "bytes are not the expected size"
        );

        let mut res = [Limb::ZERO; LIMBS];
        let mut buf = [0u8; Limb::BYTES];
        let mut i = 0;
        let mut err = 0;

        while i < LIMBS {
            let mut j = 0;
            while j < Limb::BYTES {
                let offset = (i * Limb::BYTES + j) * 2;
                let (result, byte_err) = decode_hex_byte([bytes[offset], bytes[offset + 1]]);
                err |= byte_err;
                buf[j] = result;
                j += 1;
            }
            res[i] = Limb(Word::from_le_bytes(buf));
            i += 1;
        }

        assert!(err == 0, "invalid hex byte");

        Uint::new(res)
    }

    /// Serialize this [`Uint`] as big-endian, writing it into the provided
    /// byte slice.
    #[cfg(feature = "hybrid-array")]
    #[inline]
    pub(crate) fn write_be_bytes(&self, out: &mut [u8]) {
        debug_assert_eq!(out.len(), Limb::BYTES * LIMBS);

        for (src, dst) in self
            .limbs
            .iter()
            .rev()
            .cloned()
            .zip(out.chunks_exact_mut(Limb::BYTES))
        {
            dst.copy_from_slice(&src.to_be_bytes());
        }
    }

    /// Serialize this [`Uint`] as little-endian, writing it into the provided
    /// byte slice.
    #[cfg(feature = "hybrid-array")]
    #[inline]
    pub(crate) fn write_le_bytes(&self, out: &mut [u8]) {
        debug_assert_eq!(out.len(), Limb::BYTES * LIMBS);

        for (src, dst) in self
            .limbs
            .iter()
            .cloned()
            .zip(out.chunks_exact_mut(Limb::BYTES))
        {
            dst.copy_from_slice(&src.to_le_bytes());
        }
    }

    /// Create a new [`Uint`] from a string slice in a given base.
    ///
    /// The string may begin with a `+` character, and may use
    /// underscore characters to separate digits.
    ///
    /// If the input value contains non-digit characters or digits outside of the range `0..radix`
    /// this function will return [`DecodeError::InvalidDigit`].
    /// If the size of the decoded integer is larger than this type can represent,
    /// this function will return [`DecodeError::InputSize`].
    /// Panics if `radix` is not in the range from 2 to 36.
    pub fn from_str_radix_vartime(src: &str, radix: u32) -> Result<Self, DecodeError> {
        let mut slf = Self::ZERO;
        decode_str_radix(src, radix, &mut SliceDecodeByLimb::new(&mut slf.limbs))?;
        Ok(slf)
    }
}

/// Encode a [`Uint`] to a big endian byte array of the given size.
pub(crate) const fn uint_to_be_bytes<const LIMBS: usize, const BYTES: usize>(
    uint: &Uint<LIMBS>,
) -> [u8; BYTES] {
    if BYTES != LIMBS * Limb::BYTES {
        panic!("BYTES != LIMBS * Limb::BYTES");
    }

    let mut ret = [0u8; BYTES];
    let mut i = 0;

    while i < LIMBS {
        let limb_bytes = uint.limbs[LIMBS - i - 1].0.to_be_bytes();
        let mut j = 0;

        while j < Limb::BYTES {
            ret[i * Limb::BYTES + j] = limb_bytes[j];
            j += 1;
        }

        i += 1;
    }

    ret
}

/// Encode a [`Uint`] to a little endian byte array of the given size.
pub(crate) const fn uint_to_le_bytes<const LIMBS: usize, const BYTES: usize>(
    uint: &Uint<LIMBS>,
) -> [u8; BYTES] {
    if BYTES != LIMBS * Limb::BYTES {
        panic!("BYTES != LIMBS * Limb::BYTES");
    }

    let mut ret = [0u8; BYTES];
    let mut i = 0;

    while i < LIMBS {
        let limb_bytes = uint.limbs[i].0.to_le_bytes();
        let mut j = 0;

        while j < Limb::BYTES {
            ret[i * Limb::BYTES + j] = limb_bytes[j];
            j += 1;
        }

        i += 1;
    }

    ret
}

/// Decode a single nibble of upper or lower hex
#[inline(always)]
const fn decode_nibble(src: u8) -> u16 {
    let byte = src as i16;
    let mut ret: i16 = -1;

    // 0-9  0x30-0x39
    // if (byte > 0x2f && byte < 0x3a) ret += byte - 0x30 + 1; // -47
    ret += (((0x2fi16 - byte) & (byte - 0x3a)) >> 8) & (byte - 47);
    // A-F  0x41-0x46
    // if (byte > 0x40 && byte < 0x47) ret += byte - 0x41 + 10 + 1; // -54
    ret += (((0x40i16 - byte) & (byte - 0x47)) >> 8) & (byte - 54);
    // a-f  0x61-0x66
    // if (byte > 0x60 && byte < 0x67) ret += byte - 0x61 + 10 + 1; // -86
    ret += (((0x60i16 - byte) & (byte - 0x67)) >> 8) & (byte - 86);

    ret as u16
}

/// Decode a single byte encoded as two hexadecimal characters.
/// Second element of the tuple is non-zero if the `bytes` values are not in the valid range
/// (0-9, a-z, A-Z).
#[inline(always)]
pub(crate) const fn decode_hex_byte(bytes: [u8; 2]) -> (u8, u16) {
    let hi = decode_nibble(bytes[0]);
    let lo = decode_nibble(bytes[1]);
    let byte = (hi << 4) | lo;
    let err = byte >> 8;
    let result = byte as u8;
    (result, err)
}

/// Allow decoding of integers into fixed and variable-length types
pub(crate) trait DecodeByLimb {
    /// Access the limbs as a mutable slice
    fn limbs_mut(&mut self) -> &mut [Limb];

    /// Append a new most-significant limb
    fn push_limb(&mut self, limb: Limb) -> bool;
}

/// Wrap a `Limb`` slice as a target for decoding
pub(crate) struct SliceDecodeByLimb<'de> {
    limbs: &'de mut [Limb],
    len: usize,
}

impl<'de> SliceDecodeByLimb<'de> {
    #[inline]
    pub fn new(limbs: &'de mut [Limb]) -> Self {
        Self { limbs, len: 0 }
    }
}

impl DecodeByLimb for SliceDecodeByLimb<'_> {
    #[inline]
    fn push_limb(&mut self, limb: Limb) -> bool {
        if self.len < self.limbs.len() {
            self.limbs[self.len] = limb;
            self.len += 1;
            true
        } else {
            false
        }
    }

    #[inline]
    fn limbs_mut(&mut self) -> &mut [Limb] {
        &mut self.limbs[..self.len]
    }
}

/// Decode an ascii string in base `radix`, writing the result
/// to the `DecodeByLimb` instance `out`.
/// The input must be a non-empty ascii string, may begin with a `+`
/// character, and may use `_` as a separator between digits.
pub(crate) fn decode_str_radix<D: DecodeByLimb>(
    src: &str,
    radix: u32,
    out: &mut D,
) -> Result<(), DecodeError> {
    if !(2u32..=36).contains(&radix) {
        panic!("unsupported radix");
    }
    if radix == 2 || radix == 4 || radix == 16 {
        decode_str_radix_aligned_digits(src, radix as u8, out)
    } else {
        decode_str_radix_digits(src, radix as u8, out)
    }
}

#[inline(always)]
/// Perform basic validation and pre-processing on a digit string
fn process_radix_str(src: &str) -> Result<&[u8], DecodeError> {
    // Treat the input as ascii bytes
    let src_b = src.as_bytes();
    let mut digits = src_b.strip_prefix(b"+").unwrap_or(src_b);

    if digits.is_empty() {
        // Blank string or plain "+" not allowed
        Err(DecodeError::Empty)
    } else if digits.starts_with(b"_") || digits.ends_with(b"_") {
        // Leading or trailing underscore not allowed
        Err(DecodeError::InvalidDigit)
    } else {
        // Strip leading zeroes to simplify parsing
        while digits[0] == b'0' || digits[0] == b'_' {
            digits = &digits[1..];
            if digits.is_empty() {
                break;
            }
        }
        Ok(digits)
    }
}

// Decode a string of digits in base `radix`
fn decode_str_radix_digits<D: DecodeByLimb>(
    src: &str,
    radix: u8,
    out: &mut D,
) -> Result<(), DecodeError> {
    let digits = process_radix_str(src)?;
    let mut buf = [0u8; Limb::BITS as _];
    let mut limb_digits = Word::MAX.ilog(radix as _) as usize;
    let mut limb_max = Limb(Word::pow(radix as _, limb_digits as _));
    let mut digits_pos = 0;
    let mut buf_pos = 0;

    while digits_pos < digits.len() {
        // Parse digits from most significant, to fill buffer limb
        loop {
            let digit = match digits[digits_pos] {
                b @ b'0'..=b'9' => b - b'0',
                b @ b'a'..=b'z' => b + 10 - b'a',
                b @ b'A'..=b'Z' => b + 10 - b'A',
                b'_' => {
                    digits_pos += 1;
                    continue;
                }
                _ => radix,
            };
            if digit >= radix {
                return Err(DecodeError::InvalidDigit);
            }
            buf[buf_pos] = digit;
            buf_pos += 1;
            digits_pos += 1;

            if digits_pos == digits.len() || buf_pos == limb_digits {
                break;
            }
        }

        // On the final loop, there may be fewer digits to process
        if buf_pos < limb_digits {
            limb_digits = buf_pos;
            limb_max = Limb(Word::pow(radix as _, limb_digits as _));
        }

        // Combine the digit bytes into a limb
        let mut carry = Limb::ZERO;
        for c in buf[..limb_digits].iter().copied() {
            carry = Limb(carry.0 * (radix as Word) + (c as Word));
        }
        // Multiply the existing limbs by `radix` ^ `limb_digits`,
        // and add the new least-significant limb
        for limb in out.limbs_mut().iter_mut() {
            (*limb, carry) = Limb::ZERO.mac(*limb, limb_max, carry);
        }
        // Append the new carried limb, if any
        if carry.0 != 0 && !out.push_limb(carry) {
            return Err(DecodeError::InputSize);
        }

        buf_pos = 0;
        buf[..limb_digits].fill(0);
    }

    Ok(())
}

// Decode digits for bases where an integer number of characters
// can represent a saturated Limb (specifically 2, 4, and 16).
fn decode_str_radix_aligned_digits<D: DecodeByLimb>(
    src: &str,
    radix: u8,
    out: &mut D,
) -> Result<(), DecodeError> {
    debug_assert!(radix == 2 || radix == 4 || radix == 16);

    let digits = process_radix_str(src)?;
    let shift = radix.trailing_zeros();
    let limb_digits = (Limb::BITS / shift) as usize;
    let mut buf = [0u8; Limb::BITS as _];
    let mut buf_pos = 0;
    let mut digits_pos = digits.len();

    while digits_pos > 0 {
        // Parse digits from the least significant, to fill the buffer limb
        loop {
            digits_pos -= 1;

            let digit = match digits[digits_pos] {
                b @ b'0'..=b'9' => b - b'0',
                b @ b'a'..=b'z' => b + 10 - b'a',
                b @ b'A'..=b'Z' => b + 10 - b'A',
                b'_' => {
                    // cannot occur when c == 0
                    continue;
                }
                _ => radix,
            };
            if digit >= radix {
                return Err(DecodeError::InvalidDigit);
            }
            buf[buf_pos] = digit;
            buf_pos += 1;

            if digits_pos == 0 || buf_pos == limb_digits {
                break;
            }
        }

        if buf_pos > 0 {
            // Combine the digit bytes into a limb
            let mut w: Word = 0;
            for c in buf[..buf_pos].iter().rev().copied() {
                w = (w << shift) | (c as Word);
            }
            // Append the new most-significant limb
            if !out.push_limb(Limb(w)) {
                return Err(DecodeError::InputSize);
            }

            buf_pos = 0;
            buf[..limb_digits].fill(0);
        }
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use crate::{DecodeError, Limb, Zero, U128, U64};
    use hex_literal::hex;

    #[cfg(feature = "alloc")]
    use alloc::format;

    #[cfg(target_pointer_width = "32")]
    use crate::U64 as UintEx;

    #[cfg(target_pointer_width = "64")]
    use crate::U128 as UintEx;

    #[test]
    #[cfg(target_pointer_width = "32")]
    fn from_be_slice() {
        let bytes = hex!("0011223344556677");
        let n = UintEx::from_be_slice(&bytes);
        assert_eq!(n.as_limbs(), &[Limb(0x44556677), Limb(0x00112233)]);
    }

    #[test]
    #[cfg(target_pointer_width = "64")]
    fn from_be_slice() {
        let bytes = hex!("00112233445566778899aabbccddeeff");
        let n = UintEx::from_be_slice(&bytes);
        assert_eq!(
            n.as_limbs(),
            &[Limb(0x8899aabbccddeeff), Limb(0x0011223344556677)]
        );
    }

    #[test]
    #[cfg(target_pointer_width = "32")]
    fn from_le_slice() {
        let bytes = hex!("7766554433221100");
        let n = UintEx::from_le_slice(&bytes);
        assert_eq!(n.as_limbs(), &[Limb(0x44556677), Limb(0x00112233)]);
    }

    #[test]
    #[cfg(target_pointer_width = "64")]
    fn from_le_slice() {
        let bytes = hex!("ffeeddccbbaa99887766554433221100");
        let n = UintEx::from_le_slice(&bytes);
        assert_eq!(
            n.as_limbs(),
            &[Limb(0x8899aabbccddeeff), Limb(0x0011223344556677)]
        );
    }

    #[test]
    #[cfg(target_pointer_width = "32")]
    fn from_be_hex() {
        let n = UintEx::from_be_hex("0011223344556677");
        assert_eq!(n.as_limbs(), &[Limb(0x44556677), Limb(0x00112233)]);
    }

    #[test]
    #[cfg(target_pointer_width = "64")]
    fn from_be_hex() {
        let n = UintEx::from_be_hex("00112233445566778899aabbccddeeff");
        assert_eq!(
            n.as_limbs(),
            &[Limb(0x8899aabbccddeeff), Limb(0x0011223344556677)]
        );
    }

    #[test]
    #[cfg(target_pointer_width = "32")]
    fn from_le_hex() {
        let n = UintEx::from_le_hex("7766554433221100");
        assert_eq!(n.as_limbs(), &[Limb(0x44556677), Limb(0x00112233)]);
    }

    #[test]
    #[cfg(target_pointer_width = "64")]
    fn from_le_hex() {
        let n = UintEx::from_le_hex("ffeeddccbbaa99887766554433221100");
        assert_eq!(
            n.as_limbs(),
            &[Limb(0x8899aabbccddeeff), Limb(0x0011223344556677)]
        );
    }

    #[cfg(feature = "alloc")]
    #[test]
    fn hex_upper() {
        let hex = "AAAAAAAABBBBBBBBCCCCCCCCDDDDDDDD";
        let n = U128::from_be_hex(hex);
        assert_eq!(hex, format!("{:X}", n));
    }

    #[cfg(feature = "alloc")]
    #[test]
    fn hex_lower() {
        let hex = "aaaaaaaabbbbbbbbccccccccdddddddd";
        let n = U128::from_be_hex(hex);
        assert_eq!(hex, format!("{:x}", n));
    }

    #[cfg(feature = "alloc")]
    #[test]
    fn fmt_binary() {
        let hex = "AAAAAAAABBBBBBBBCCCCCCCCDDDDDDDD";
        let n = U128::from_be_hex(hex);
        let expect = "\
            1010101010101010101010101010101010111011101110111011101110111011\
            1100110011001100110011001100110011011101110111011101110111011101";
        assert_eq!(expect, format!("{:b}", n));
    }

    #[test]
    fn from_str_radix_disallowed() {
        let tests = [
            ("", 10, DecodeError::Empty),
            ("+", 10, DecodeError::Empty),
            ("_", 10, DecodeError::InvalidDigit),
            ("0_", 10, DecodeError::InvalidDigit),
            ("0_", 10, DecodeError::InvalidDigit),
            ("a", 10, DecodeError::InvalidDigit),
            (".", 10, DecodeError::InvalidDigit),
            (
                "99999999999999999999999999999999",
                10,
                DecodeError::InputSize,
            ),
        ];
        for (input, radix, expect) in tests {
            assert_eq!(U64::from_str_radix_vartime(input, radix), Err(expect));
        }
    }

    #[test]
    fn from_str_radix_2() {
        let buf = &[b'1'; 128];
        let radix = U128::from_u64(2);
        let radix_max = U128::from_u64(1);
        let mut last: Option<U128> = None;
        for idx in (1..buf.len()).rev() {
            let res = U128::from_str_radix_vartime(
                core::str::from_utf8(&buf[..idx]).expect("utf-8 error"),
                2,
            )
            .expect("error decoding");
            assert!(!bool::from(res.is_zero()));
            if let Some(prev) = last {
                assert_eq!(res.saturating_mul(&radix).saturating_add(&radix_max), prev);
            }
            last = Some(res);
        }
        assert_eq!(last, Some(radix_max));
    }

    #[test]
    fn from_str_radix_5() {
        let buf = &[b'4'; 55];
        let radix = U128::from_u64(5);
        let radix_max = U128::from_u64(4);
        let mut last: Option<U128> = None;
        for idx in (1..buf.len()).rev() {
            let res = U128::from_str_radix_vartime(
                core::str::from_utf8(&buf[..idx]).expect("utf-8 error"),
                5,
            )
            .expect("error decoding");
            assert!(!bool::from(res.is_zero()));
            if let Some(prev) = last {
                assert_eq!(res.saturating_mul(&radix).saturating_add(&radix_max), prev);
            }
            last = Some(res);
        }
        assert_eq!(last, Some(radix_max));
    }

    #[test]
    fn from_str_radix_10() {
        let dec = "+340_282_366_920_938_463_463_374_607_431_768_211_455";
        let res = U128::from_str_radix_vartime(dec, 10).expect("error decoding");
        assert_eq!(res, U128::MAX);
    }

    #[cfg(feature = "alloc")]
    #[test]
    fn from_str_radix_16() {
        let hex = "fedcba9876543210fedcba9876543210";
        let res = U128::from_str_radix_vartime(hex, 16).expect("error decoding");
        assert_eq!(hex, format!("{res:x}"));
    }
}
