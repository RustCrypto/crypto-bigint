//! Stack-allocated big signed integers.

use core::fmt;

use num_traits::ConstZero;
#[cfg(feature = "serde")]
use serdect::serde::{Deserialize, Deserializer, Serialize, Serializer};
use subtle::{Choice, ConditionallySelectable, ConstantTimeEq};

use crate::{
    Bounded, ConstChoice, ConstCtOption, Constants, Encoding, Limb, NonZero, Odd, Uint, Word,
};

#[macro_use]
mod macros;

mod add;
mod cmp;
mod div;
mod encoding;
mod from;
mod mul;
mod neg;
mod resize;
mod sign;
mod sub;

#[cfg(feature = "rand_core")]
mod rand;

/// Stack-allocated big _signed_ integer.
/// See [`Uint`] for _unsigned_ integers.
///
/// Created as a [`Uint`] newtype.
#[allow(clippy::derived_hash_with_manual_eq)]
#[derive(Copy, Clone, Hash)]
pub struct Int<const LIMBS: usize>(Uint<LIMBS>);

impl<const LIMBS: usize> Int<LIMBS> {
    /// The value `0`.
    pub const ZERO: Self = Self(Uint::ZERO); // Bit sequence (be): 0000....0000

    /// The value `1`.
    pub const ONE: Self = Self(Uint::ONE); // Bit sequence (be): 0000....0001

    /// The value `-1`
    pub const MINUS_ONE: Self = Self::FULL_MASK; // Bit sequence (be): 1111....1111

    /// Smallest value this [`Int`] can express.
    pub const MIN: Self = Self(Uint::MAX.bitxor(&Uint::MAX.shr(1u32))); // Bit sequence (be): 1000....0000

    /// Maximum value this [`Int`] can express.
    pub const MAX: Self = Self(Uint::MAX.shr(1u32)); // Bit sequence (be): 0111....1111

    /// Bit mask for the sign bit of this [`Int`].
    pub const SIGN_MASK: Self = Self::MIN; // Bit sequence (be): 1000....0000

    /// All-one bit mask.
    pub const FULL_MASK: Self = Self(Uint::MAX); // Bit sequence (be): 1111...1111

    /// Total size of the represented integer in bits.
    pub const BITS: u32 = Uint::<LIMBS>::BITS;

    /// Total size of the represented integer in bytes.
    pub const BYTES: usize = Uint::<LIMBS>::BYTES;

    /// The number of limbs used on this platform.
    pub const LIMBS: usize = LIMBS;

    /// Const-friendly [`Int`] constructor.
    pub const fn new(limbs: [Limb; LIMBS]) -> Self {
        Self(Uint::new(limbs))
    }

    /// Const-friendly [`Int`] constructor.
    /// Note: interprets the `value` as an `Int`. For a proper conversion,
    /// see [`Int::new_from_abs_sign`].
    pub const fn new_from_uint(value: Uint<LIMBS>) -> Self {
        Self(value)
    }

    /// Create an [`Int`] from an array of [`Word`]s (i.e. word-sized unsigned
    /// integers).
    #[inline]
    pub const fn from_words(arr: [Word; LIMBS]) -> Self {
        Self(Uint::from_words(arr))
    }

    /// Create an array of [`Word`]s (i.e. word-sized unsigned integers) from
    /// an [`Int`].
    #[inline]
    pub const fn to_words(self) -> [Word; LIMBS] {
        self.0.to_words()
    }

    /// Borrow the inner limbs as an array of [`Word`]s.
    pub const fn as_words(&self) -> &[Word; LIMBS] {
        self.0.as_words()
    }

    /// Borrow the inner limbs as a mutable array of [`Word`]s.
    pub fn as_words_mut(&mut self) -> &mut [Word; LIMBS] {
        self.0.as_words_mut()
    }

    /// Borrow the limbs of this [`Int`].
    pub const fn as_limbs(&self) -> &[Limb; LIMBS] {
        self.0.as_limbs()
    }

    /// Borrow the limbs of this [`Int`] mutably.
    pub fn as_limbs_mut(&mut self) -> &mut [Limb; LIMBS] {
        self.0.as_limbs_mut()
    }

    /// Convert this [`Int`] into its inner limbs.
    pub const fn to_limbs(self) -> [Limb; LIMBS] {
        self.0.to_limbs()
    }

    /// Convert to a [`NonZero<Int<LIMBS>>`].
    ///
    /// Returns some if the original value is non-zero, and false otherwise.
    pub const fn to_nz(self) -> ConstCtOption<NonZero<Self>> {
        ConstCtOption::new(NonZero(self), self.0.is_nonzero())
    }

    /// Convert to a [`Odd<Int<LIMBS>>`].
    ///
    /// Returns some if the original value is odd, and false otherwise.
    pub const fn to_odd(self) -> ConstCtOption<Odd<Self>> {
        ConstCtOption::new(Odd(self), self.0.is_odd())
    }

    /// Interpret the data in this type as a [`Uint`] instead.
    pub const fn as_uint(&self) -> &Uint<LIMBS> {
        &self.0
    }

    /// Whether this [`Int`] is equal to `Self::MIN`.
    pub fn is_min(&self) -> ConstChoice {
        Self::eq(self, &Self::MIN)
    }

    /// Whether this [`Int`] is equal to `Self::MAX`.
    pub fn is_max(&self) -> ConstChoice {
        Self::eq(self, &Self::MAX)
    }

    /// Invert the most significant bit (msb) of this [`Int`]
    const fn invert_msb(&self) -> Self {
        Self(self.0.bitxor(&Self::SIGN_MASK.0))
    }
}

impl<const LIMBS: usize> AsRef<[Word; LIMBS]> for Int<LIMBS> {
    fn as_ref(&self) -> &[Word; LIMBS] {
        self.as_words()
    }
}

impl<const LIMBS: usize> AsMut<[Word; LIMBS]> for Int<LIMBS> {
    fn as_mut(&mut self) -> &mut [Word; LIMBS] {
        self.as_words_mut()
    }
}

impl<const LIMBS: usize> AsRef<[Limb]> for Int<LIMBS> {
    fn as_ref(&self) -> &[Limb] {
        self.as_limbs()
    }
}

impl<const LIMBS: usize> AsMut<[Limb]> for Int<LIMBS> {
    fn as_mut(&mut self) -> &mut [Limb] {
        self.as_limbs_mut()
    }
}

impl<const LIMBS: usize> ConditionallySelectable for Int<LIMBS> {
    fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
        Self(Uint::conditional_select(&a.0, &b.0, choice))
    }
}

impl<const LIMBS: usize> Bounded for Int<LIMBS> {
    const BITS: u32 = Self::BITS;
    const BYTES: usize = Self::BYTES;
}

impl<const LIMBS: usize> Constants for Int<LIMBS> {
    const ONE: Self = Self::ONE;
    const MAX: Self = Self::MAX;
}

impl<const LIMBS: usize> Default for Int<LIMBS> {
    fn default() -> Self {
        Self::ZERO
    }
}

// TODO: impl FixedInteger

// TODO: impl Integer

impl<const LIMBS: usize> ConstZero for Int<LIMBS> {
    const ZERO: Self = Self::ZERO;
}

impl<const LIMBS: usize> num_traits::Zero for Int<LIMBS> {
    fn zero() -> Self {
        Self::ZERO
    }

    fn is_zero(&self) -> bool {
        self.0.ct_eq(&Self::ZERO.0).into()
    }
}

impl<const LIMBS: usize> num_traits::One for Int<LIMBS> {
    fn one() -> Self {
        Self::ONE
    }

    fn is_one(&self) -> bool {
        self.0.ct_eq(&Self::ONE.0).into()
    }
}

impl<const LIMBS: usize> fmt::Debug for Int<LIMBS> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Int(0x{self:X})")
    }
}

impl<const LIMBS: usize> fmt::Binary for Int<LIMBS> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Binary::fmt(&self.0, f)
    }
}

impl<const LIMBS: usize> fmt::Display for Int<LIMBS> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::UpperHex::fmt(self, f)
    }
}

impl<const LIMBS: usize> fmt::LowerHex for Int<LIMBS> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::LowerHex::fmt(&self.0, f)
    }
}

impl<const LIMBS: usize> fmt::UpperHex for Int<LIMBS> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::UpperHex::fmt(&self.0, f)
    }
}

#[cfg(feature = "serde")]
impl<'de, const LIMBS: usize> Deserialize<'de> for Int<LIMBS>
where
    Int<LIMBS>: Encoding,
{
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let mut buffer = Self::ZERO.to_le_bytes();
        serdect::array::deserialize_hex_or_bin(buffer.as_mut(), deserializer)?;
        Ok(Self::from_le_bytes(buffer))
    }
}

#[cfg(feature = "serde")]
impl<const LIMBS: usize> Serialize for Int<LIMBS>
where
    Int<LIMBS>: Encoding,
{
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        serdect::array::serialize_hex_lower_or_bin(&Encoding::to_le_bytes(self), serializer)
    }
}

impl_int_aliases! {
    (I64, 64, "64-bit"),
    (I128, 128, "128-bit"),
    (I192, 192, "192-bit"),
    (I256, 256, "256-bit"),
    (I320, 320, "320-bit"),
    (I384, 384, "384-bit"),
    (I448, 448, "448-bit"),
    (I512, 512, "512-bit"),
    (I576, 576, "576-bit"),
    (I640, 640, "640-bit"),
    (I704, 704, "704-bit"),
    (I768, 768, "768-bit"),
    (I832, 832, "832-bit"),
    (I896, 896, "896-bit"),
    (I960, 960, "960-bit"),
    (I1024, 1024, "1024-bit"),
    (I1280, 1280, "1280-bit"),
    (I1536, 1536, "1536-bit"),
    (I1792, 1792, "1792-bit"),
    (I2048, 2048, "2048-bit"),
    (I3072, 3072, "3072-bit"),
    (I3584, 3584, "3584-bit"),
    (I4096, 4096, "4096-bit"),
    (I4224, 4224, "4224-bit"),
    (I4352, 4352, "4352-bit"),
    (I6144, 6144, "6144-bit"),
    (I8192, 8192, "8192-bit"),
    (I16384, 16384, "16384-bit"),
    (I32768, 32768, "32768-bit")
}

#[cfg(test)]
#[allow(clippy::unwrap_used)]
mod tests {
    use subtle::ConditionallySelectable;

    use crate::int::I128;
    use crate::ConstChoice;
    #[cfg(feature = "serde")]
    use crate::U128;

    #[cfg(target_pointer_width = "64")]
    #[test]
    fn as_words() {
        let n = I128::from_be_hex("AAAAAAAABBBBBBBBCCCCCCCCDDDDDDDD");
        assert_eq!(n.as_words(), &[0xCCCCCCCCDDDDDDDD, 0xAAAAAAAABBBBBBBB]);
    }

    #[cfg(target_pointer_width = "64")]
    #[test]
    fn as_words_mut() {
        let mut n = I128::from_be_hex("AAAAAAAABBBBBBBBCCCCCCCCDDDDDDDD");
        assert_eq!(n.as_words_mut(), &[0xCCCCCCCCDDDDDDDD, 0xAAAAAAAABBBBBBBB]);
    }

    #[cfg(feature = "alloc")]
    #[test]
    fn debug() {
        let n = I128::from_be_hex("AAAAAAAABBBBBBBBCCCCCCCCDDDDDDDD");

        assert_eq!(
            format!("{:?}", n),
            "Int(0xAAAAAAAABBBBBBBBCCCCCCCCDDDDDDDD)"
        );
    }

    #[cfg(feature = "alloc")]
    #[test]
    fn display() {
        let hex = "AAAAAAAABBBBBBBBCCCCCCCCDDDDDDDD";
        let n = I128::from_be_hex(hex);

        use alloc::string::ToString;
        assert_eq!(hex, n.to_string());

        let hex = "AAAAAAAABBBBBBBB0000000000000000";
        let n = I128::from_be_hex(hex);
        assert_eq!(hex, n.to_string());

        let hex = "AAAAAAAABBBBBBBB00000000DDDDDDDD";
        let n = I128::from_be_hex(hex);
        assert_eq!(hex, n.to_string());

        let hex = "AAAAAAAABBBBBBBB0CCCCCCCDDDDDDDD";
        let n = I128::from_be_hex(hex);
        assert_eq!(hex, n.to_string());
    }

    #[test]
    fn conditional_select() {
        let a = I128::from_be_hex("00002222444466668888AAAACCCCEEEE");
        let b = I128::from_be_hex("11113333555577779999BBBBDDDDFFFF");

        let select_0 = I128::conditional_select(&a, &b, 0.into());
        assert_eq!(a, select_0);

        let select_1 = I128::conditional_select(&a, &b, 1.into());
        assert_eq!(b, select_1);
    }

    #[test]
    fn is_minimal() {
        let min = I128::from_be_hex("80000000000000000000000000000000");
        assert_eq!(min.is_min(), ConstChoice::TRUE);

        let random = I128::from_be_hex("11113333555577779999BBBBDDDDFFFF");
        assert_eq!(random.is_min(), ConstChoice::FALSE);
    }

    #[test]
    fn is_maximal() {
        let max = I128::from_be_hex("7FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF");
        assert_eq!(max.is_max(), ConstChoice::TRUE);

        let random = I128::from_be_hex("11113333555577779999BBBBDDDDFFFF");
        assert_eq!(random.is_max(), ConstChoice::FALSE);
    }

    #[cfg(feature = "serde")]
    #[test]
    fn serde() {
        const TEST: I128 = I128::new_from_uint(U128::from_u64(0x0011223344556677));

        let serialized = bincode::serialize(&TEST).unwrap();
        let deserialized: I128 = bincode::deserialize(&serialized).unwrap();

        assert_eq!(TEST, deserialized);
    }

    #[cfg(feature = "serde")]
    #[test]
    fn serde_owned() {
        const TEST: I128 = I128::new_from_uint(U128::from_u64(0x0011223344556677));

        let serialized = bincode::serialize(&TEST).unwrap();
        let deserialized: I128 = bincode::deserialize_from(serialized.as_slice()).unwrap();

        assert_eq!(TEST, deserialized);
    }
}
