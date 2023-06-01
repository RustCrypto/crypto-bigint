//! Support for base-10 parsing and encoding.

use core::{f32::consts::LOG10_2, fmt, fmt::Display, slice::RChunks, str};

#[cfg(feature = "alloc")]
use alloc::{borrow::Cow, string::String, vec::Vec};
#[cfg(feature = "serde")]
use core::marker::PhantomData;

#[cfg(feature = "serde")]
use serdect::serde::{
    de::{Error, Unexpected, Visitor},
    Deserialize, Deserializer, Serialize, Serializer,
};

use crate::{div_limb, uint::bits::bits_vartime, Limb, Reciprocal, Uint, Word};

#[cfg(feature = "alloc")]
use crate::BoxedUint;

#[cfg(target_pointer_width = "64")]
const LIMB_LOG10: usize = 19;
#[cfg(not(target_pointer_width = "64"))]
const LIMB_LOG10: usize = 9;

const LIMB_MAX10: Limb = Limb(Word::pow(10, LIMB_LOG10 as u32));
const LIMB_MAX10_RECIP: Reciprocal = Reciprocal::ct_new(LIMB_MAX10).0;

#[derive(Copy, Eq, PartialEq, Clone, Debug)]
/// The failure result for decimal parsing operations.
pub enum ParseDecimalError {
    /// The input was not a numeric string
    InvalidInput,
    /// The value cannot be contained in this data type
    OutsideRange,
}

impl Display for ParseDecimalError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidInput => write!(f, "invalid input"),
            Self::OutsideRange => write!(f, "exceeded maximum length"),
        }
    }
}

/// Support for parsing decimal strings
pub trait FromDecimal: Sized {
    /// Parse an instance of this data type from a decimal string
    fn from_decimal(value: &str) -> Result<Self, ParseDecimalError> {
        Self::from_decimal_bytes(value.as_bytes())
    }

    /// Parse an instance of this data type from a string of utf-8 bytes
    fn from_decimal_bytes(value: &[u8]) -> Result<Self, ParseDecimalError>;
}

impl<const LIMBS: usize> FromDecimal for Uint<LIMBS> {
    fn from_decimal_bytes(value: &[u8]) -> Result<Self, ParseDecimalError> {
        let mut res = Self::ZERO;
        ParseDecimal::parse_into(value, res.as_limbs_mut())?;
        Ok(res)
    }
}

#[cfg(feature = "alloc")]
impl FromDecimal for BoxedUint {
    fn from_decimal_bytes(value: &[u8]) -> Result<Self, ParseDecimalError> {
        let parse = ParseDecimal::new(value)?;
        let bits = parse.len() * Limb::BITS;
        if bits > 0 {
            let mut res = BoxedUint::new(bits).expect("Error creating boxed uint");
            parse.read_into(res.as_limbs_mut())?;
            Ok(res)
        } else {
            Ok(BoxedUint::zero())
        }
    }
}

struct ParseDecimal<'p>(RChunks<'p, u8>);

impl<'p> ParseDecimal<'p> {
    pub(crate) fn new(dec: &'p [u8]) -> Result<Self, ParseDecimalError> {
        if dec.is_empty() {
            return Err(ParseDecimalError::InvalidInput);
        }
        let mut start = dec.len();
        for (idx, c) in dec.iter().enumerate().rev() {
            if !matches!(c, b'0'..=b'9') {
                return Err(ParseDecimalError::InvalidInput);
            }
            if *c != b'0' {
                start = idx;
            }
        }
        Ok(Self(dec[start..].rchunks(LIMB_LOG10)))
    }

    pub(crate) fn parse_into(dec: &'p [u8], limbs: &mut [Limb]) -> Result<(), ParseDecimalError> {
        Self::new(dec)?.read_into(limbs)
    }

    pub(crate) fn read_into(self, limbs: &mut [Limb]) -> Result<(), ParseDecimalError> {
        for l in limbs.iter_mut() {
            *l = Limb::ZERO;
        }
        for (idx, mut carry) in self.enumerate() {
            for i in 0..=(idx + 1).min(limbs.len() - 1) {
                let (l, c) = Limb::ZERO.mac(limbs[i], LIMB_MAX10, carry);
                limbs[i] = l;
                carry = c;
            }
            if carry.0 != 0 {
                return Err(ParseDecimalError::OutsideRange);
            }
        }
        Ok(())
    }
}

impl Iterator for ParseDecimal<'_> {
    type Item = Limb;

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next_back().map(|chunk| {
            let w: Word = chunk
                .into_iter()
                .fold(0, |acc, c| acc * 10 + ((c - b'0') as Word));
            Limb(w)
        })
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }
}

impl ExactSizeIterator for ParseDecimal<'_> {}

#[cfg(feature = "serde")]
#[derive(Default)]
struct DecimalUintVisitor<T>(PhantomData<T>);

#[cfg(feature = "serde")]
impl<T: FromDecimal> Visitor<'_> for DecimalUintVisitor<T> {
    type Value = T;

    fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "a decimal string")
    }

    fn visit_str<E>(self, dec: &str) -> Result<Self::Value, E>
    where
        E: Error,
    {
        T::from_decimal(dec).map_err(|_| E::invalid_value(Unexpected::Str(dec), &self))
    }
}

/// Deserialize a type supporting `FromDecimal` from a decimal string.
/// This method may be used as a field decorator when using serde-derive.
#[cfg(feature = "serde")]
pub fn deserialize<'de, D, T>(deserializer: D) -> Result<T, D::Error>
where
    D: Deserializer<'de>,
    T: FromDecimal,
{
    deserializer.deserialize_str(DecimalUintVisitor(PhantomData))
}

/// Serialize an integer to a decimal string. This method may be used
/// as a field decorator when using serde-derive.
#[cfg(all(feature = "serde", feature = "alloc"))]
pub fn serialize<S, T>(uint: &T, serializer: S) -> Result<S::Ok, S::Error>
where
    S: Serializer,
    T: AsRef<[Limb]> + AsMut<[Limb]> + Clone,
{
    _with_decimal_str(uint, |buf| serializer.serialize_str(buf))
}

/// A wrapper type for a `Uint` or `BoxedUint` which is formatted
/// in decimal digits.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AsDecimal<T>(pub T);

#[cfg(feature = "alloc")]
impl<const LIMBS: usize> Display for AsDecimal<&Uint<LIMBS>> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        _with_decimal_str(self.0, |buf| f.write_str(buf))
    }
}

#[cfg(feature = "alloc")]
impl<const LIMBS: usize> Display for AsDecimal<Uint<LIMBS>> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        Display::fmt(&AsDecimal(&self.0), f)
    }
}

#[cfg(feature = "alloc")]
impl Display for AsDecimal<&BoxedUint> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        _with_decimal_str(self.0, |buf| f.write_str(buf))
    }
}

#[cfg(feature = "alloc")]
impl Display for AsDecimal<BoxedUint> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        Display::fmt(&AsDecimal(&self.0), f)
    }
}

#[cfg(feature = "serde")]
impl<'de, T: FromDecimal> Deserialize<'de> for AsDecimal<T> {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        Ok(Self(deserialize(deserializer)?))
    }
}

#[cfg(feature = "serde")]
impl<'s, T> Serialize for AsDecimal<T>
where
    AsDecimal<T>: Display,
{
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        serializer.collect_str(self)
    }
}

/// Output the decimal digits of `uint` to `buf`.
/// This algorithm repeatedly divides by the largest power of 10 that
/// fits into a limb, and fills the buffer backwards from the end
/// using the digits of the remainder.
fn _encode_decimal_limbs(uint: &mut [Limb], buf: &mut [u8]) {
    const SHIFT: u32 = LIMB_MAX10_RECIP.shift;
    const RSHIFT: u32 = if SHIFT == 0 {
        0
    } else {
        Limb::BITS as u32 - SHIFT
    };

    let mut pos = buf.len();
    while pos > 0 {
        let (len, rem) = if pos > LIMB_LOG10 {
            // Modified `div_rem_limb_with_reciprocal`: divide `uint` in place.
            let mut carry: u64 = 0;
            if SHIFT != 0 {
                for limb in uint.iter_mut() {
                    let r = (limb.0 << SHIFT) | carry;
                    carry = r >> RSHIFT;
                    *limb = Limb(r);
                }
            }
            for limb in uint.iter_mut().rev() {
                let (qj, rj) = div_limb::div2by1(carry, limb.0, &LIMB_MAX10_RECIP);
                *limb = Limb(qj);
                carry = rj;
            }
            (LIMB_LOG10, Limb(carry))
        } else {
            let l = uint[0];
            uint[0] = Limb::ZERO;
            (pos, l)
        };
        _encode_remainder_limb(rem, &mut buf[(pos - len)..pos]);
        pos -= len;
    }
}

/// Obtain the decimal representation of an integer as a vector
/// of ASCII bytes.
#[cfg(feature = "alloc")]
pub fn to_decimal_vec<T>(uint: &T) -> Vec<u8>
where
    T: AsRef<[Limb]> + AsMut<[Limb]> + Clone,
{
    let digits = _max_digits(bits_vartime(uint.as_ref()));
    if digits == 0 {
        return Vec::from([b'0']);
    }
    let mut res = Vec::new();
    res.resize(digits, b'0');
    let len = _write_decimal_bytes(uint, &mut res);
    res.truncate(len);
    res
}

/// Obtain the decimal representation of an integer as a String.
#[cfg(feature = "alloc")]
pub fn to_decimal_string<T>(uint: &T) -> String
where
    T: AsRef<[Limb]> + AsMut<[Limb]> + Clone,
{
    String::from_utf8(to_decimal_vec(uint)).expect("Error converting to utf-8")
}

/// Write the decimal representation of `uint` to a provided buffer,
/// returning the length of the output. If the output is too large for the
/// buffer, then zero is returned.
pub fn write_decimal_bytes<T>(uint: &T, buf: &mut [u8]) -> usize
where
    T: AsRef<[Limb]> + AsMut<[Limb]> + Clone,
{
    let digits = _max_digits(bits_vartime(uint.as_ref()));
    if digits.max(1) > buf.len() {
        return 0;
    }
    if digits == 0 {
        buf[0] = b'0';
        return 1;
    }
    _write_decimal_bytes(uint, &mut buf[..digits])
}

fn _write_decimal_bytes<T>(uint: &T, buf: &mut [u8]) -> usize
where
    T: AsRef<[Limb]> + AsMut<[Limb]> + Clone,
{
    let mut rem = 0;
    let digits = buf.len();
    if digits < LIMB_LOG10 {
        let len = _encode_remainder_limb(uint.as_ref()[0], buf);
        rem = digits - len;
    } else {
        let mut work = uint.clone();
        _encode_decimal_limbs(work.as_mut(), buf);
        while buf[rem] == b'0' {
            rem += 1;
        }
    }
    if rem > 0 {
        buf.copy_within(rem..digits, 0);
        buf[(digits - rem)..digits].fill(b'0');
    }
    digits - rem
}

#[cfg(feature = "alloc")]
fn _with_decimal_str<T, F, R>(uint: &T, f: F) -> R
where
    F: FnOnce(&str) -> R,
    T: AsRef<[Limb]> + AsMut<[Limb]> + Clone,
{
    const BUF_SIZE: usize = 2560;
    let mut buf = [0u8; BUF_SIZE];
    let cow = _to_decimal_bytes_cow(uint, &mut buf);
    let s = str::from_utf8(cow.as_ref()).expect("Error converting to utf-8");
    f(s)
}

#[cfg(feature = "alloc")]
fn _to_decimal_bytes_cow<'b, T>(uint: &T, buf: &'b mut [u8]) -> Cow<'b, [u8]>
where
    T: AsRef<[Limb]> + AsMut<[Limb]> + Clone,
{
    let digits = _max_digits(bits_vartime(uint.as_ref()));
    if digits == 0 {
        return Cow::Borrowed(b"0");
    }
    let mut vec = Vec::new();
    let write = if digits > buf.len() {
        vec.resize(digits, b'0');
        vec.as_mut_slice()
    } else {
        &mut buf[..digits]
    };
    let len = _write_decimal_bytes(uint, write);
    if !vec.is_empty() {
        vec.truncate(len);
        Cow::Owned(vec)
    } else {
        Cow::Borrowed(&buf[..len])
    }
}

#[inline]
fn _encode_remainder_limb(mut limb: Limb, buf: &mut [u8]) -> usize {
    let mut pos = buf.len();
    while limb.0 > 0 && pos > 0 {
        pos -= 1;
        buf[pos] = ('0' as u8) + (limb.0 % 10) as u8;
        limb = Limb(limb.0 / 10);
    }
    let nz_len = buf.len() - pos;
    while pos > 0 {
        pos -= 1;
        buf[pos] = '0' as u8;
    }
    nz_len
}

#[inline]
fn _max_digits(bits: usize) -> usize {
    ((bits as f32) * LOG10_2).ceil() as usize
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Integer, Random};
    use core::fmt::Debug;

    #[test]
    fn decode_empty() {
        let res = crate::U64::from_decimal("");
        assert_eq!(res, Err(ParseDecimalError::InvalidInput));
    }

    #[test]
    fn decode_invalid() {
        let res = crate::U64::from_decimal("000notanumber");
        assert_eq!(res, Err(ParseDecimalError::InvalidInput));
    }

    #[test]
    fn decode_outside_range() {
        let res = crate::U64::from_decimal("18446744073709551616"); // 2^64
        assert_eq!(res, Err(ParseDecimalError::OutsideRange));
    }

    fn _round_trip_uint<T>(uint: &T)
    where
        T: AsRef<[Limb]> + AsMut<[Limb]> + Clone + Debug + FromDecimal + PartialEq,
    {
        let mut buf = [0u8; 2560];
        let len = write_decimal_bytes(uint, &mut buf);
        let des = T::from_decimal_bytes(&buf[..len]).expect("Error deserializing");
        assert_eq!(&des, uint);
    }

    fn _round_trip_test<T>(n: usize)
    where
        T: AsRef<[Limb]> + AsMut<[Limb]> + Clone + FromDecimal + Integer + Random,
    {
        _round_trip_uint(&T::ZERO);
        _round_trip_uint(&T::ONE);
        _round_trip_uint(&T::MAX);
        use rand_core::SeedableRng;
        let mut rng = rand_chacha::ChaCha8Rng::seed_from_u64(1);
        for _ in 0..n {
            let uint = T::random(&mut rng);
            _round_trip_uint(&uint);
        }
    }

    #[test]
    fn round_trip_u64() {
        _round_trip_test::<crate::U64>(10000)
    }

    #[test]
    fn round_trip_u1024() {
        _round_trip_test::<crate::U1024>(1000)
    }

    #[test]
    fn round_trip_u8192() {
        _round_trip_test::<crate::U8192>(100)
    }

    #[cfg(feature = "alloc")]
    #[test]
    fn round_trip_boxed() {
        _round_trip_uint(&BoxedUint::zero());
        _round_trip_uint(&BoxedUint::one());
        _round_trip_uint(&BoxedUint::max(2048).unwrap());
    }

    #[cfg(all(feature = "serde", feature = "alloc"))]
    #[test]
    fn serde_uint() {
        type U = crate::U128;
        let input = "123456789012345678901234567890";
        let uint = U::from_decimal(input).unwrap();
        let enc = bincode::serialize(&AsDecimal(&uint)).unwrap();
        let dec: String = bincode::deserialize(&enc).unwrap();
        assert_eq!(dec, input);
        let des: AsDecimal<U> = bincode::deserialize(&enc).unwrap();
        assert_eq!(des.0, uint);
    }

    #[cfg(all(feature = "serde", feature = "alloc"))]
    #[test]
    fn serde_boxed() {
        let input = "123456789012345678901234567890";
        let uint = BoxedUint::from_decimal(input).unwrap();
        let enc = bincode::serialize(&AsDecimal(&uint)).unwrap();
        let dec: String = bincode::deserialize(&enc).unwrap();
        assert_eq!(dec, input);
        let des: AsDecimal<BoxedUint> = bincode::deserialize(&enc).unwrap();
        assert_eq!(des.0, uint);
    }
}
