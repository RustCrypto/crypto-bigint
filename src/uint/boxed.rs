//! Heap-allocated big unsigned integers.

mod add;
mod add_mod;
mod bit_and;
mod bit_not;
mod bit_or;
mod bit_xor;
mod bits;
mod cmp;
mod ct;
pub(crate) mod div;
mod div_limb;
pub(crate) mod encoding;
mod from;
mod gcd;
mod invert_mod;
mod mul;
mod mul_mod;
mod neg;
mod neg_mod;
mod shl;
mod shr;
mod sqrt;
mod sub;
mod sub_mod;

#[cfg(feature = "rand_core")]
mod rand;

use crate::{Integer, Limb, NonZero, Odd, Resize, UintRef, Word, Zero, modular::BoxedMontyForm};
use alloc::{boxed::Box, vec, vec::Vec};
use core::fmt;
use subtle::{Choice, ConditionallySelectable, ConstantTimeEq, CtOption};

#[cfg(feature = "zeroize")]
use zeroize::Zeroize;

/// Fixed-precision heap-allocated big unsigned integer.
///
/// Alternative to the stack-allocated [`Uint`][`crate::Uint`] but with a
/// fixed precision chosen at runtime instead of compile time.
///
/// Unlike many other heap-allocated big integer libraries, this type is not
/// arbitrary precision and will wrap at its fixed-precision rather than
/// automatically growing.
#[allow(clippy::derived_hash_with_manual_eq)]
#[derive(Clone, Hash)]
pub struct BoxedUint {
    /// Boxed slice containing limbs.
    ///
    /// Stored from least significant to most significant.
    pub(crate) limbs: Box<[Limb]>,
}

impl BoxedUint {
    fn limbs_for_precision(at_least_bits_precision: u32) -> usize {
        at_least_bits_precision.div_ceil(Limb::BITS) as usize
    }

    /// Get the value `0` represented as succinctly as possible.
    pub fn zero() -> Self {
        Self {
            limbs: vec![Limb::ZERO; 1].into(),
        }
    }

    /// Get the value `0` with the given number of bits of precision.
    ///
    /// `at_least_bits_precision` is rounded up to a multiple of [`Limb::BITS`].
    pub fn zero_with_precision(at_least_bits_precision: u32) -> Self {
        vec![Limb::ZERO; Self::limbs_for_precision(at_least_bits_precision)].into()
    }

    /// Get the value `1`, represented as succinctly as possible.
    pub fn one() -> Self {
        Self {
            limbs: vec![Limb::ONE; 1].into(),
        }
    }

    /// Get the value `1` with the given number of bits of precision.
    ///
    /// `at_least_bits_precision` is rounded up to a multiple of [`Limb::BITS`].
    pub fn one_with_precision(at_least_bits_precision: u32) -> Self {
        let mut ret = Self::zero_with_precision(at_least_bits_precision);
        ret.limbs[0] = Limb::ONE;
        ret
    }

    /// Is this [`BoxedUint`] equal to zero?
    pub fn is_zero(&self) -> Choice {
        self.limbs
            .iter()
            .fold(Choice::from(1), |acc, limb| acc & limb.is_zero())
    }

    /// Is this [`BoxedUint`] *NOT* equal to zero?
    #[inline]
    pub fn is_nonzero(&self) -> Choice {
        !self.is_zero()
    }

    /// Is this [`BoxedUint`] equal to one?
    pub fn is_one(&self) -> Choice {
        let mut iter = self.limbs.iter();
        let choice = iter.next().copied().unwrap_or(Limb::ZERO).ct_eq(&Limb::ONE);
        iter.fold(choice, |acc, limb| acc & limb.is_zero())
    }

    /// Get the maximum value for a `BoxedUint` created with `at_least_bits_precision`
    /// precision bits requested.
    ///
    /// That is, returns the value `2^self.bits_precision() - 1`.
    pub fn max(at_least_bits_precision: u32) -> Self {
        vec![Limb::MAX; Self::limbs_for_precision(at_least_bits_precision)].into()
    }

    /// Create a [`BoxedUint`] from an array of [`Word`]s (i.e. word-sized unsigned
    /// integers).
    #[inline]
    pub fn from_words(words: impl IntoIterator<Item = Word>) -> Self {
        Self {
            limbs: words.into_iter().map(Into::into).collect(),
        }
    }

    /// Create a boxed slice of [`Word`]s (i.e. word-sized unsigned integers) from
    /// a [`BoxedUint`].
    #[inline]
    pub fn to_words(&self) -> Box<[Word]> {
        self.limbs.iter().copied().map(Into::into).collect()
    }

    /// Borrow the inner limbs as a slice of [`Word`]s.
    pub fn as_words(&self) -> &[Word] {
        self.as_uint_ref().as_words()
    }

    /// Borrow the inner limbs as a mutable slice of [`Word`]s.
    pub fn as_mut_words(&mut self) -> &mut [Word] {
        self.as_mut_uint_ref().as_mut_words()
    }

    /// Borrow the inner limbs as a mutable slice of [`Word`]s.
    #[deprecated(since = "0.7.0", note = "please use `as_mut_words` instead")]
    pub fn as_words_mut(&mut self) -> &mut [Word] {
        self.as_mut_words()
    }

    /// Borrow the limbs of this [`BoxedUint`].
    pub fn as_limbs(&self) -> &[Limb] {
        self.limbs.as_ref()
    }

    /// Borrow the limbs of this [`BoxedUint`] mutably.
    pub fn as_mut_limbs(&mut self) -> &mut [Limb] {
        self.limbs.as_mut()
    }

    /// Borrow the limbs of this [`BoxedUint`] mutably.
    #[deprecated(since = "0.7.0", note = "please use `as_mut_limbs` instead")]
    pub fn as_limbs_mut(&mut self) -> &mut [Limb] {
        self.as_mut_limbs()
    }

    /// Convert this [`BoxedUint`] into its inner limbs.
    pub fn to_limbs(&self) -> Box<[Limb]> {
        self.limbs.clone()
    }

    /// Convert this [`BoxedUint`] into its inner limbs.
    pub fn into_limbs(self) -> Box<[Limb]> {
        self.limbs
    }

    /// Borrow the limbs of this [`BoxedUint`] as a [`UintRef`].
    pub(crate) fn as_uint_ref(&self) -> &UintRef {
        UintRef::new(&self.limbs)
    }

    /// Mutably borrow the limbs of this [`BoxedUint`] as a [`UintRef`].
    pub(crate) fn as_mut_uint_ref(&mut self) -> &mut UintRef {
        UintRef::new_mut(&mut self.limbs)
    }

    /// Get the number of limbs in this [`BoxedUint`].
    pub fn nlimbs(&self) -> usize {
        self.limbs.len()
    }

    /// Convert into an [`Odd`].
    pub fn to_odd(&self) -> CtOption<Odd<Self>> {
        let is_odd = self.is_odd();
        CtOption::new(Odd(self.clone()), is_odd)
    }

    /// Widen this type's precision to the given number of bits.
    ///
    /// Panics if `at_least_bits_precision` is smaller than the current precision.
    #[must_use]
    #[deprecated(since = "0.7.0", note = "please use `resize` instead")]
    pub fn widen(&self, at_least_bits_precision: u32) -> BoxedUint {
        assert!(at_least_bits_precision >= self.bits_precision());

        let mut ret = BoxedUint::zero_with_precision(at_least_bits_precision);
        ret.limbs[..self.nlimbs()].copy_from_slice(&self.limbs);
        ret
    }

    /// Shortens this type's precision to the given number of bits.
    ///
    /// Panics if `at_least_bits_precision` is larger than the current precision.
    #[must_use]
    #[deprecated(since = "0.7.0", note = "please use `resize` instead")]
    pub fn shorten(&self, at_least_bits_precision: u32) -> BoxedUint {
        assert!(at_least_bits_precision <= self.bits_precision());
        let mut ret = BoxedUint::zero_with_precision(at_least_bits_precision);
        let nlimbs = ret.nlimbs();
        ret.limbs.copy_from_slice(&self.limbs[..nlimbs]);
        ret
    }

    /// Perform a carry chain-like operation over the limbs of the inputs,
    /// constructing a result from the returned limbs and carry which is
    /// widened to the same width as the widest input.
    ///
    /// If one of the two values has fewer limbs than the other, pads with
    /// [`Limb::ZERO`] as the value for that limb.
    #[inline]
    fn fold_limbs<F>(lhs: &Self, rhs: &Self, mut carry: Limb, f: F) -> (Self, Limb)
    where
        F: Fn(Limb, Limb, Limb) -> (Limb, Limb),
    {
        let nlimbs = cmp::max(lhs.nlimbs(), rhs.nlimbs());
        let mut limbs = Vec::with_capacity(nlimbs);

        for i in 0..nlimbs {
            let &a = lhs.limbs.get(i).unwrap_or(&Limb::ZERO);
            let &b = rhs.limbs.get(i).unwrap_or(&Limb::ZERO);
            let (limb, c) = f(a, b, carry);
            limbs.push(limb);
            carry = c;
        }

        (limbs.into(), carry)
    }

    /// Iterate over the limbs of the inputs, applying the given function, and
    /// constructing a result from the returned values.
    #[inline]
    fn map_limbs<F>(lhs: &Self, rhs: &Self, f: F) -> Self
    where
        F: Fn(Limb, Limb) -> Limb,
    {
        let nlimbs = cmp::max(lhs.nlimbs(), rhs.nlimbs());
        let mut limbs = Vec::with_capacity(nlimbs);

        for i in 0..nlimbs {
            let &a = lhs.limbs.get(i).unwrap_or(&Limb::ZERO);
            let &b = rhs.limbs.get(i).unwrap_or(&Limb::ZERO);
            limbs.push(f(a, b));
        }

        limbs.into()
    }

    /// Set the value of `self` to zero in-place if `choice` is truthy.
    pub(crate) fn conditional_set_zero(&mut self, choice: Choice) {
        let nlimbs = self.nlimbs();
        let limbs = self.limbs.as_mut();
        for i in 0..nlimbs {
            limbs[i] = Limb::conditional_select(&limbs[i], &Limb::ZERO, choice);
        }
    }

    /// Returns `true` if the integer's bit size is smaller or equal to `bits`.
    pub(crate) fn is_within_bits(&self, bits: u32) -> bool {
        bits >= self.bits_precision() || bits >= self.bits()
    }
}

impl Resize for BoxedUint {
    type Output = BoxedUint;

    fn resize_unchecked(self, at_least_bits_precision: u32) -> Self::Output {
        let new_len = Self::limbs_for_precision(at_least_bits_precision);
        if new_len == self.limbs.len() {
            self
        } else {
            let mut limbs = self.limbs.into_vec();
            limbs.resize(new_len, Limb::ZERO);
            Self::from(limbs)
        }
    }

    fn try_resize(self, at_least_bits_precision: u32) -> Option<BoxedUint> {
        if self.is_within_bits(at_least_bits_precision) {
            Some(self.resize_unchecked(at_least_bits_precision))
        } else {
            None
        }
    }
}

impl Resize for &BoxedUint {
    type Output = BoxedUint;

    fn resize_unchecked(self, at_least_bits_precision: u32) -> Self::Output {
        let mut ret = BoxedUint::zero_with_precision(at_least_bits_precision);
        let num_limbs_to_copy = core::cmp::min(ret.limbs.len(), self.limbs.len());
        ret.limbs[..num_limbs_to_copy].copy_from_slice(&self.limbs[..num_limbs_to_copy]);
        ret
    }

    fn try_resize(self, at_least_bits_precision: u32) -> Option<BoxedUint> {
        if self.is_within_bits(at_least_bits_precision) {
            Some(self.resize_unchecked(at_least_bits_precision))
        } else {
            None
        }
    }
}

impl Resize for NonZero<BoxedUint> {
    type Output = Self;

    fn resize_unchecked(self, at_least_bits_precision: u32) -> Self::Output {
        NonZero(self.0.resize_unchecked(at_least_bits_precision))
    }

    fn try_resize(self, at_least_bits_precision: u32) -> Option<Self::Output> {
        self.0.try_resize(at_least_bits_precision).map(NonZero)
    }
}

impl Resize for &NonZero<BoxedUint> {
    type Output = NonZero<BoxedUint>;

    fn resize_unchecked(self, at_least_bits_precision: u32) -> Self::Output {
        NonZero((&self.0).resize_unchecked(at_least_bits_precision))
    }

    fn try_resize(self, at_least_bits_precision: u32) -> Option<Self::Output> {
        (&self.0).try_resize(at_least_bits_precision).map(NonZero)
    }
}

impl AsRef<[Word]> for BoxedUint {
    fn as_ref(&self) -> &[Word] {
        self.as_words()
    }
}

impl AsMut<[Word]> for BoxedUint {
    fn as_mut(&mut self) -> &mut [Word] {
        self.as_mut_words()
    }
}

impl AsRef<[Limb]> for BoxedUint {
    fn as_ref(&self) -> &[Limb] {
        self.as_limbs()
    }
}

impl AsMut<[Limb]> for BoxedUint {
    fn as_mut(&mut self) -> &mut [Limb] {
        self.as_mut_limbs()
    }
}

impl AsRef<UintRef> for BoxedUint {
    fn as_ref(&self) -> &UintRef {
        self.as_uint_ref()
    }
}

impl AsMut<UintRef> for BoxedUint {
    fn as_mut(&mut self) -> &mut UintRef {
        self.as_mut_uint_ref()
    }
}

impl Default for BoxedUint {
    fn default() -> Self {
        Self::zero()
    }
}

impl Integer for BoxedUint {
    type Monty = BoxedMontyForm;

    fn one() -> Self {
        Self::one()
    }

    fn from_limb_like(limb: Limb, other: &Self) -> Self {
        let mut ret = Self::zero_with_precision(other.bits_precision());
        ret.limbs[0] = limb;
        ret
    }

    fn nlimbs(&self) -> usize {
        self.nlimbs()
    }
}

impl Zero for BoxedUint {
    fn zero() -> Self {
        Self::zero()
    }

    fn is_zero(&self) -> Choice {
        self.is_zero()
    }

    fn set_zero(&mut self) {
        self.limbs.as_mut().fill(Limb::ZERO)
    }
}

impl num_traits::Zero for BoxedUint {
    fn zero() -> Self {
        Self::zero()
    }

    fn is_zero(&self) -> bool {
        self.is_zero().into()
    }
}

impl num_traits::One for BoxedUint {
    fn one() -> Self {
        Self::one()
    }

    fn is_one(&self) -> bool {
        self.is_one().into()
    }
}

#[cfg(feature = "zeroize")]
impl Zeroize for BoxedUint {
    fn zeroize(&mut self) {
        self.limbs.zeroize();
    }
}

impl fmt::Debug for BoxedUint {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "BoxedUint(0x{:X})", self.as_uint_ref())
    }
}

impl fmt::Display for BoxedUint {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::UpperHex::fmt(self, f)
    }
}

impl fmt::Binary for BoxedUint {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Binary::fmt(self.as_uint_ref(), f)
    }
}

impl fmt::LowerHex for BoxedUint {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::LowerHex::fmt(self.as_uint_ref(), f)
    }
}

impl fmt::UpperHex for BoxedUint {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::UpperHex::fmt(self.as_uint_ref(), f)
    }
}

#[cfg(test)]
mod tests {
    use super::BoxedUint;
    use crate::Word;
    use alloc::vec::Vec;

    #[test]
    fn from_word_vec() {
        let words: &[Word] = &[0, 1, 2, 3];
        let uint = BoxedUint::from(Vec::from(words));
        assert_eq!(uint.nlimbs(), 4);
        assert_eq!(uint.as_words(), words);
    }

    #[test]
    fn fmt_lower_hex() {
        let n = BoxedUint::from_be_hex("AAAAAAAABBBBBBBBCCCCCCCCDDDDDDDD", 128).unwrap();
        assert_eq!(format!("{n:x}"), "aaaaaaaabbbbbbbbccccccccdddddddd");
        assert_eq!(format!("{n:#x}"), "0xaaaaaaaabbbbbbbbccccccccdddddddd");
    }

    #[test]
    fn fmt_upper_hex() {
        let n = BoxedUint::from_be_hex("aaaaaaaabbbbbbbbccccccccdddddddd", 128).unwrap();
        assert_eq!(format!("{n:X}"), "AAAAAAAABBBBBBBBCCCCCCCCDDDDDDDD");
        assert_eq!(format!("{n:#X}"), "0xAAAAAAAABBBBBBBBCCCCCCCCDDDDDDDD");
    }

    #[test]
    fn fmt_binary() {
        let n = BoxedUint::from_be_hex("aaaaaaaabbbbbbbbccccccccdddddddd", 128).unwrap();
        assert_eq!(
            format!("{n:b}"),
            "10101010101010101010101010101010101110111011101110111011101110111100110011001100110011001100110011011101110111011101110111011101"
        );
        assert_eq!(
            format!("{n:#b}"),
            "0b10101010101010101010101010101010101110111011101110111011101110111100110011001100110011001100110011011101110111011101110111011101"
        );
    }
}
