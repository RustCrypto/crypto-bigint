//! Big integers are represented as an array of smaller CPU word-size integers
//! called "limbs".

mod add;
mod bit_and;
mod bit_not;
mod bit_or;
mod bit_xor;
mod bits;
mod cmp;
mod encoding;
mod from;
mod mul;
mod neg;
mod shl;
mod shr;
mod sub;

#[cfg(feature = "rand_core")]
mod rand;

use crate::{
    Bounded, ConstChoice, ConstCtOption, ConstOne, ConstZero, Constants, CtEq, NonZero, One,
    WideWord, Word, Zero, word,
};
use core::fmt;
use ctutils::CtSelect;
use subtle::Choice;

#[cfg(feature = "serde")]
use serdect::serde::{Deserialize, Deserializer, Serialize, Serializer};

/// Big integers are represented as an array/vector of smaller CPU word-size integers called
/// "limbs".
///
/// The [`Limb`] type uses a 32-bit or 64-bit saturated representation, depending on the target.
/// All bits of an inner [`Word`] are used to represent larger big integer types.
// Our PartialEq impl only differs from the default one by being constant-time, so this is safe
#[allow(clippy::derived_hash_with_manual_eq)]
#[derive(Copy, Clone, Default, Hash)]
#[repr(transparent)]
pub struct Limb(pub Word);

impl Limb {
    /// The value `0`.
    pub const ZERO: Self = Limb(0);

    /// The value `1`.
    pub const ONE: Self = Limb(1);

    /// Maximum value this [`Limb`] can express.
    pub const MAX: Self = Limb(Word::MAX);

    /// Highest bit in a [`Limb`].
    pub(crate) const HI_BIT: u32 = Limb::BITS - 1;

    // 32-bit

    /// Size of the inner integer in bits.
    #[cfg(target_pointer_width = "32")]
    pub const BITS: u32 = 32;
    /// Size of the inner integer in bytes.
    #[cfg(target_pointer_width = "32")]
    pub const BYTES: usize = 4;

    // 64-bit

    /// Size of the inner integer in bits.
    #[cfg(target_pointer_width = "64")]
    pub const BITS: u32 = 64;
    /// Size of the inner integer in bytes.
    #[cfg(target_pointer_width = "64")]
    pub const BYTES: usize = 8;

    /// `floor(log2(Self::BITS))`.
    pub const LOG2_BITS: u32 = u32::BITS - (Self::BITS - 1).leading_zeros();

    /// Is this limb equal to [`Limb::ZERO`]?
    pub const fn is_zero(&self) -> ConstChoice {
        word::choice_from_nz(self.0).not()
    }

    /// Convert to a [`NonZero<Limb>`].
    ///
    /// Returns some if the original value is non-zero, and false otherwise.
    pub const fn to_nz(self) -> ConstCtOption<NonZero<Self>> {
        let is_nz = self.is_nonzero();

        // Use `1` as a placeholder in the event that `self` is `Limb(0)`
        let nz_word = word::select(1, self.0, is_nz);
        ConstCtOption::new(NonZero(Self(nz_word)), is_nz)
    }
}

impl Bounded for Limb {
    const BITS: u32 = Self::BITS;
    const BYTES: usize = Self::BYTES;
}

impl Constants for Limb {
    const MAX: Self = Self::MAX;
}

impl subtle::ConditionallySelectable for Limb {
    #[inline]
    fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
        a.ct_select(b, choice.into())
    }
}

impl CtSelect for Limb {
    #[inline]
    fn ct_select(&self, other: &Self, choice: ConstChoice) -> Self {
        Self(self.0.ct_select(&other.0, choice))
    }
}

impl ConstZero for Limb {
    const ZERO: Self = Self::ZERO;
}

impl ConstOne for Limb {
    const ONE: Self = Self::ONE;
}

impl Zero for Limb {
    #[inline(always)]
    fn zero() -> Self {
        Self::ZERO
    }
}

impl One for Limb {
    #[inline(always)]
    fn one() -> Self {
        Self::ONE
    }
}

impl num_traits::Zero for Limb {
    fn zero() -> Self {
        Self::ZERO
    }

    fn is_zero(&self) -> bool {
        self.ct_eq(&Self::ZERO).into()
    }
}

impl num_traits::One for Limb {
    fn one() -> Self {
        Self::ONE
    }

    fn is_one(&self) -> bool {
        self.ct_eq(&Self::ONE).into()
    }
}

impl fmt::Debug for Limb {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Limb(0x{self:X})")
    }
}

impl fmt::Display for Limb {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::UpperHex::fmt(self, f)
    }
}

impl fmt::Binary for Limb {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if f.alternate() {
            write!(f, "0b")?;
        }

        write!(f, "{:0width$b}", &self.0, width = Self::BITS as usize)
    }
}

impl fmt::LowerHex for Limb {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if f.alternate() {
            write!(f, "0x")?;
        }
        write!(f, "{:0width$x}", &self.0, width = Self::BYTES * 2)
    }
}

impl fmt::UpperHex for Limb {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if f.alternate() {
            write!(f, "0x")?;
        }
        write!(f, "{:0width$X}", &self.0, width = Self::BYTES * 2)
    }
}

#[cfg(feature = "serde")]
impl<'de> Deserialize<'de> for Limb {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        Ok(Self(Word::deserialize(deserializer)?))
    }
}

#[cfg(feature = "serde")]
impl Serialize for Limb {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        self.0.serialize(serializer)
    }
}

#[cfg(feature = "zeroize")]
impl zeroize::DefaultIsZeroes for Limb {}

#[cfg(test)]
mod tests {
    #[cfg(feature = "alloc")]
    use {super::Limb, alloc::format};

    #[cfg(feature = "alloc")]
    #[test]
    fn debug() {
        #[cfg(target_pointer_width = "32")]
        assert_eq!(format!("{:?}", Limb(42)), "Limb(0x0000002A)");

        #[cfg(target_pointer_width = "64")]
        assert_eq!(format!("{:?}", Limb(42)), "Limb(0x000000000000002A)");
    }
}
