use core::{fmt, ops::Not};

use subtle::{Choice, ConditionallySelectable, CtOption};

use crate::{Bounded, ConstCtOption, Limb, NonZero, Odd, Uint, Word};

mod encoding;

/// Stack-allocated big _signed_ integer.
/// See [`Uint`] for _unsigned_ integers.
///
/// Created as a [`Uint`] newtype.
#[derive(Copy, Clone, PartialEq, Hash)]
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
    pub const SIGN_BIT_MASK: Self = Self::MIN; // Bit sequence (be): 1000....0000

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

    /// Compute the sign bit of this [`Int`].
    ///
    /// Returns some if the original value is odd, and false otherwise.
    pub const fn sign_bit(&self) -> Word {
        self.0.bitand(&Self::SIGN_BIT_MASK.0).to_words()[LIMBS - 1] >> (Word::BITS - 1)
    }

    /// View the data in this type as an [`Uint`] instead.
    pub const fn as_uint(&self) -> Uint<LIMBS> {
        self.0
    }

    /// Whether this [`Int`] is equal to Self::MIN.
    pub fn is_minimal(&self) -> Choice {
        Choice::from((self == &Self::MIN) as u8)
    }

    /// Whether this [`Int`] is equal to Self::MIN.
    pub fn is_maximal(&self) -> Choice {
        Choice::from((self == &Self::MAX) as u8)
    }

    /// Map this [`Int`] to `-self` if possible.
    pub fn negated(&self) -> CtOption<Int<LIMBS>> {
        CtOption::new(
            Self(self.0.bitxor(&Self::FULL_MASK.0).wrapping_add(&Self::ONE.0)),
            self.is_minimal().not(),
        )
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

// TODO: impl Constants

impl<const LIMBS: usize> Default for Int<LIMBS> {
    fn default() -> Self {
        Self::ZERO
    }
}

// TODO: impl FixedInteger

// TODO: impl Integer

// TODO: impl ConstZero

// TODO: impl num_traits::One

// TODO: impl num_traits::One

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

#[cfg(test)]
#[allow(clippy::unwrap_used)]
mod tests {
    use subtle::ConditionallySelectable;

    use crate::Int;

    type I128 = Int<2>;

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
    fn sign_bit() {
        assert_eq!(I128::MIN.sign_bit(), 1u32.into());
        assert_eq!(I128::MINUS_ONE.sign_bit(), 1u32.into());
        assert_eq!(I128::ZERO.sign_bit(), 0u32.into());
        assert_eq!(I128::ONE.sign_bit(), 0u32.into());
        assert_eq!(I128::MAX.sign_bit(), 0u32.into());

        let random_negative = I128::from_be_hex("91113333555577779999BBBBDDDDFFFF");
        assert_eq!(random_negative.sign_bit(), 1u32.into());

        let random_positive = I128::from_be_hex("71113333555577779999BBBBDDDDFFFF");
        assert_eq!(random_positive.sign_bit(), 0u32.into());
    }

    #[test]
    fn is_minimal() {
        let min = I128::from_be_hex("80000000000000000000000000000000");
        assert_eq!(min.is_minimal().unwrap_u8(), 1u8);

        let random = I128::from_be_hex("11113333555577779999BBBBDDDDFFFF");
        assert_eq!(random.is_minimal().unwrap_u8(), 0u8);
    }

    #[test]
    fn is_maximal() {
        let max = I128::from_be_hex("7FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF");
        assert_eq!(max.is_maximal().unwrap_u8(), 1u8);

        let random = I128::from_be_hex("11113333555577779999BBBBDDDDFFFF");
        assert_eq!(random.is_maximal().unwrap_u8(), 0u8);
    }

    #[test]
    fn negated() {
        assert_eq!(I128::MIN.negated().is_none().unwrap_u8(), 1u8);
        assert_eq!(I128::MINUS_ONE.negated().unwrap(), I128::ONE);
        assert_eq!(I128::ZERO.negated().unwrap(), I128::ZERO);
        assert_eq!(I128::ONE.negated().unwrap(), I128::MINUS_ONE);
        assert_eq!(
            I128::MAX.negated().unwrap(),
            I128::from_be_hex("80000000000000000000000000000001")
        );

        let negative = I128::from_be_hex("91113333555577779999BBBBDDDDFFFF");
        let positive = I128::from_be_hex("6EEECCCCAAAA88886666444422220001");
        assert_eq!(negative.negated().unwrap(), positive);
        assert_eq!(positive.negated().unwrap(), negative);
        assert_eq!(positive.negated().unwrap().negated().unwrap(), positive);
    }
}
