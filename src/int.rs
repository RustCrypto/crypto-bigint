use core::fmt;

use subtle::{Choice, ConditionallySelectable, ConstantTimeEq, ConstantTimeGreater, CtOption};

use crate::{Bounded, ConstantTimeSelect, ConstChoice, ConstCtOption, Limb, NonZero, Odd, Uint, Word};

mod encoding;
mod add;
mod mul;

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

    /// Construct new [`Int`] from a sign and magnitude.
    /// Returns `None` when the magnitude does not fit in an [`Int<LIMBS>`].
    pub fn new_from_sign_and_magnitude(is_negative: Choice, magnitude: Uint<LIMBS>) -> CtOption<Self> {
        CtOption::new(
            Self(magnitude).negate_if_unsafe(is_negative).0,
            !magnitude.ct_gt(&Int::MAX.0) | is_negative & magnitude.ct_eq(&Int::MIN.0),
        )
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

    /// Get the sign bit of this [`Int`] as `Choice`.
    pub fn sign_bit(&self) -> Choice {
        Choice::from((self.0.to_words()[LIMBS - 1] >> (Word::BITS - 1)) as u8)
    }

    /// View the data in this type as an [`Uint`] instead.
    pub const fn as_uint(&self) -> Uint<LIMBS> {
        self.0
    }

    /// Whether this [`Int`] is equal to `Self::MIN`.
    pub fn is_minimal(&self) -> Choice {
        Choice::from((self == &Self::MIN) as u8)
    }

    /// Whether this [`Int`] is equal to `Self::MAX`.
    pub fn is_maximal(&self) -> Choice {
        Choice::from((self == &Self::MAX) as u8)
    }

    /// Perform the two's complement "negate" operation on this [`Int`]:
    /// map `self` to `(self ^ 1111...1111) + 0000...0001`
    ///
    /// Returns
    /// - the result, as well as
    /// - whether the addition overflowed (indicating `self` is zero).
    ///
    /// Warning: this operation is unsafe; when `self == Self::MIN`, the negation fails.
    #[inline]
    fn negate_unsafe(&self) -> (Self, Choice) {
        let inverted = self.0.bitxor(&Self::FULL_MASK.0);
        let (res, carry) = inverted.adc(&Uint::ONE, Limb::ZERO);
        let is_zero = ConstChoice::from_word_lsb(carry.0).into();
        (Self(res), is_zero)
    }

    /// Perform the [two's complement "negate" operation](Int::negate_unsafe) on this [`Int`]
    /// if `negate` is truthy.
    ///
    /// Returns
    /// - the result, as well as
    /// - whether the addition overflowed (indicating `self` is zero).
    ///
    /// Warning: this operation is unsafe; when `self == Self::MIN` and `negate` is truthy,
    /// the negation fails.
    #[inline]
    fn negate_if_unsafe(&self, negate: Choice) -> (Int<LIMBS>, Choice) {
        let (negated, is_zero) = self.negate_unsafe();
        (Self(Uint::ct_select(&self.0, &negated.0, negate)), is_zero)
    }

    /// Map this [`Int`] to `-self` if possible.
    ///
    /// Yields `None` when `self == Self::MIN`, since an [`Int`] cannot represent the positive
    /// equivalent of that.
    pub fn neg(&self) -> CtOption<Self> {
        CtOption::new(
            self.negate_unsafe().0,
            !self.is_minimal()
        )
    }

    /// The sign and magnitude of this [`Int`], as well as whether it is zero.
    pub fn sign_magnitude_is_zero(&self) -> (Choice, Uint<LIMBS>, Choice) {
        let sign = self.sign_bit();
        let (magnitude, is_zero) = self.negate_if_unsafe(sign);
        (sign, magnitude.0, is_zero)
    }

    /// The magnitude of this [`Int`].
    pub fn magnitude(&self) -> Uint<LIMBS> {
        self.sign_magnitude_is_zero().1
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

#[cfg(target_pointer_width = "64")]
type I128 = Int<2>;

#[cfg(target_pointer_width = "32")]
type I128 = Int<4>;

#[cfg(test)]
#[allow(clippy::unwrap_used)]
mod tests {
    use subtle::ConditionallySelectable;

    use crate::int::I128;

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
        assert_eq!(I128::MIN.sign_bit().unwrap_u8(), 1u8);
        assert_eq!(I128::MINUS_ONE.sign_bit().unwrap_u8(), 1u8);
        assert_eq!(I128::ZERO.sign_bit().unwrap_u8(), 0u8);
        assert_eq!(I128::ONE.sign_bit().unwrap_u8(), 0u8);
        assert_eq!(I128::MAX.sign_bit().unwrap_u8(), 0u8);

        let random_negative = I128::from_be_hex("91113333555577779999BBBBDDDDFFFF");
        assert_eq!(random_negative.sign_bit().unwrap_u8(), 1u8);

        let random_positive = I128::from_be_hex("71113333555577779999BBBBDDDDFFFF");
        assert_eq!(random_positive.sign_bit().unwrap_u8(), 0u8);
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
        assert_eq!(I128::MIN.neg().is_none().unwrap_u8(), 1u8);
        assert_eq!(I128::MINUS_ONE.neg().unwrap(), I128::ONE);
        assert_eq!(I128::ZERO.neg().unwrap(), I128::ZERO);
        assert_eq!(I128::ONE.neg().unwrap(), I128::MINUS_ONE);
        assert_eq!(
            I128::MAX.neg().unwrap(),
            I128::from_be_hex("80000000000000000000000000000001")
        );

        let negative = I128::from_be_hex("91113333555577779999BBBBDDDDFFFF");
        let positive = I128::from_be_hex("6EEECCCCAAAA88886666444422220001");
        assert_eq!(negative.neg().unwrap(), positive);
        assert_eq!(positive.neg().unwrap(), negative);
        assert_eq!(positive.neg().unwrap().neg().unwrap(), positive);
    }
}
