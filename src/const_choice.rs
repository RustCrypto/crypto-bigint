use subtle::{Choice, CtOption};

use crate::{NonZero, Uint, Word};

/// A boolean value returned by constant-time `const fn`s.
// TODO: should be replaced by `subtle::Choice` or `CtOption`
// when `subtle` starts supporting const fns.
#[derive(Debug, Copy, Clone)]
pub struct ConstChoice(Word);

impl ConstChoice {
    /// The falsy value.
    pub const FALSE: Self = Self(0);

    /// The truthy value.
    pub const TRUE: Self = Self(Word::MAX);

    #[inline]
    pub(crate) const fn as_u32_mask(&self) -> u32 {
        #[allow(trivial_numeric_casts)]
        (self.0.wrapping_neg() as u32).wrapping_neg()
    }

    /// Returns the truthy value if `value == Word::MAX`, and the falsy value if `value == 0`.
    /// Panics for other values.
    #[inline]
    pub(crate) const fn from_word_mask(value: Word) -> Self {
        debug_assert!(value == Self::FALSE.0 || value == Self::TRUE.0);
        Self(value)
    }

    /// Returns the truthy value if `value == 1`, and the falsy value if `value == 0`.
    /// Panics for other values.
    #[inline]
    pub(crate) const fn from_word_lsb(value: Word) -> Self {
        debug_assert!(value == 0 || value == 1);
        Self(value.wrapping_neg())
    }

    #[inline]
    pub(crate) const fn from_u32_lsb(value: u32) -> Self {
        debug_assert!(value == 0 || value == 1);
        #[allow(trivial_numeric_casts)]
        Self((value as Word).wrapping_neg())
    }

    /// Returns the truthy value if `value != 0`, and the falsy value otherwise.
    #[inline]
    pub(crate) const fn from_u32_nonzero(value: u32) -> Self {
        Self::from_u32_lsb((value | value.wrapping_neg()) >> (u32::BITS - 1))
    }

    /// Returns the truthy value if `value != 0`, and the falsy value otherwise.
    #[inline]
    pub(crate) const fn from_word_nonzero(value: Word) -> Self {
        Self::from_word_lsb((value | value.wrapping_neg()) >> (Word::BITS - 1))
    }

    /// Returns the truthy value if `x == y`, and the falsy value otherwise.
    #[inline]
    pub(crate) const fn from_u32_eq(x: u32, y: u32) -> Self {
        Self::from_u32_nonzero(x ^ y).not()
    }

    /// Returns the truthy value if `x == y`, and the falsy value otherwise.
    #[inline]
    pub(crate) const fn from_word_eq(x: Word, y: Word) -> Self {
        Self::from_word_nonzero(x ^ y).not()
    }

    /// Returns the truthy value if `x < y`, and the falsy value otherwise.
    #[inline]
    pub(crate) const fn from_word_lt(x: Word, y: Word) -> Self {
        // See "Hacker's Delight" 2nd ed, section 2-12 (Comparison predicates)
        let bit = (((!x) & y) | (((!x) | y) & (x.wrapping_sub(y)))) >> (Word::BITS - 1);
        Self::from_word_lsb(bit)
    }

    /// Returns the truthy value if `x > y`, and the falsy value otherwise.
    #[inline]
    pub(crate) const fn from_word_gt(x: Word, y: Word) -> Self {
        // See "Hacker's Delight" 2nd ed, section 2-12 (Comparison predicates)
        let bit = (((!y) & x) | (((!y) | x) & (y.wrapping_sub(x)))) >> (Word::BITS - 1);
        Self::from_word_lsb(bit)
    }

    /// Returns the truthy value if `x < y`, and the falsy value otherwise.
    #[inline]
    pub(crate) const fn from_u32_lt(x: u32, y: u32) -> Self {
        let bit = (((!x) & y) | (((!x) | y) & (x.wrapping_sub(y)))) >> (u32::BITS - 1);
        Self::from_u32_lsb(bit)
    }

    /// Returns the truthy value if `x <= y` and the falsy value otherwise.
    #[inline]
    pub(crate) const fn from_word_le(x: Word, y: Word) -> Self {
        let bit = (((!x) | y) & ((x ^ y) | !(y.wrapping_sub(x)))) >> (Word::BITS - 1);
        Self::from_word_lsb(bit)
    }

    /// Returns the truthy value if `x <= y` and the falsy value otherwise.
    #[inline]
    pub(crate) const fn from_u32_le(x: u32, y: u32) -> Self {
        let bit = (((!x) | y) & ((x ^ y) | !(y.wrapping_sub(x)))) >> (u32::BITS - 1);
        Self::from_u32_lsb(bit)
    }

    #[inline]
    pub(crate) const fn not(&self) -> Self {
        Self(!self.0)
    }

    #[inline]
    pub(crate) const fn or(&self, other: Self) -> Self {
        Self(self.0 | other.0)
    }

    #[inline]
    pub(crate) const fn and(&self, other: Self) -> Self {
        Self(self.0 & other.0)
    }

    /// Return `b` if `self` is truthy, otherwise return `a`.
    #[inline]
    pub(crate) const fn select_word(&self, a: Word, b: Word) -> Word {
        a ^ (self.0 & (a ^ b))
    }

    /// Return `b` if `self` is truthy, otherwise return `a`.
    #[inline]
    pub(crate) const fn select_u32(&self, a: u32, b: u32) -> u32 {
        a ^ (self.as_u32_mask() & (a ^ b))
    }

    /// Return `x` if `self` is truthy, otherwise return 0.
    #[inline]
    pub(crate) const fn if_true_word(&self, x: Word) -> Word {
        x & self.0
    }

    /// Return `x` if `self` is truthy, otherwise return 0.
    #[inline]
    pub(crate) const fn if_true_u32(&self, x: u32) -> u32 {
        x & self.as_u32_mask()
    }

    #[inline]
    pub(crate) const fn is_true_vartime(&self) -> bool {
        self.0 == ConstChoice::TRUE.0
    }

    #[inline]
    pub(crate) const fn to_u8(self) -> u8 {
        (self.0 as u8) & 1
    }
}

impl From<ConstChoice> for Choice {
    #[inline]
    fn from(choice: ConstChoice) -> Self {
        Choice::from(choice.to_u8())
    }
}

impl From<ConstChoice> for bool {
    fn from(choice: ConstChoice) -> Self {
        choice.is_true_vartime()
    }
}

impl PartialEq for ConstChoice {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

/// An equivalent of `subtle::CtOption` usable in a `const fn` context.
#[derive(Debug, Clone)]
pub struct ConstOption<T> {
    value: T,
    is_some: ConstChoice,
}

impl<T> ConstOption<T> {
    #[inline]
    pub(crate) const fn new(value: T, is_some: ConstChoice) -> Self {
        Self { value, is_some }
    }

    #[inline]
    pub(crate) const fn some(value: T) -> Self {
        Self {
            value,
            is_some: ConstChoice::TRUE,
        }
    }

    #[inline]
    pub(crate) const fn none(dummy_value: T) -> Self {
        Self {
            value: dummy_value,
            is_some: ConstChoice::FALSE,
        }
    }

    /// Returns a reference to the contents of this structure.
    ///
    /// **Note:** if the second element is `None`, the first value may take any value.
    #[inline]
    pub(crate) const fn components_ref(&self) -> (&T, ConstChoice) {
        // Since Rust is not smart enough to tell that we would be moving the value,
        // and hence no destructors will be called, we have to return a reference instead.
        // See https://github.com/rust-lang/rust/issues/66753
        (&self.value, self.is_some)
    }

    /// Returns a true [`ConstChoice`] if this value is `Some`.
    #[inline]
    pub const fn is_some(&self) -> ConstChoice {
        self.is_some
    }

    /// Returns a true [`ConstChoice`] if this value is `None`.
    #[inline]
    pub const fn is_none(&self) -> ConstChoice {
        self.is_some.not()
    }

    /// This returns the underlying value but panics if it is not `Some`.
    #[inline]
    pub fn unwrap(self) -> T {
        assert!(self.is_some.is_true_vartime());
        self.value
    }
}

impl<T> From<ConstOption<T>> for CtOption<T> {
    #[inline]
    fn from(value: ConstOption<T>) -> Self {
        CtOption::new(value.value, value.is_some.into())
    }
}

// Need specific implementations to work around the
// "destructors cannot be evaluated at compile-time" error
// See https://github.com/rust-lang/rust/issues/66753

impl<const LIMBS: usize> ConstOption<Uint<LIMBS>> {
    /// This returns the underlying value if it is `Some` or the provided value otherwise.
    #[inline]
    pub const fn unwrap_or(self, def: Uint<LIMBS>) -> Uint<LIMBS> {
        Uint::select(&def, &self.value, self.is_some)
    }

    /// Returns the contained value, consuming the `self` value.
    ///
    /// # Panics
    ///
    /// Panics if the value is none with a custom panic message provided by
    /// `msg`.
    #[inline]
    pub const fn expect(self, msg: &str) -> Uint<LIMBS> {
        assert!(self.is_some.is_true_vartime(), "{}", msg);
        self.value
    }
}

impl<const LIMBS: usize> ConstOption<(Uint<LIMBS>, Uint<LIMBS>)> {
    /// Returns the contained value, consuming the `self` value.
    ///
    /// # Panics
    ///
    /// Panics if the value is none with a custom panic message provided by
    /// `msg`.
    #[inline]
    pub const fn expect(self, msg: &str) -> (Uint<LIMBS>, Uint<LIMBS>) {
        assert!(self.is_some.is_true_vartime(), "{}", msg);
        self.value
    }
}

impl<const LIMBS: usize> ConstOption<NonZero<Uint<LIMBS>>> {
    /// Returns the contained value, consuming the `self` value.
    ///
    /// # Panics
    ///
    /// Panics if the value is none with a custom panic message provided by
    /// `msg`.
    #[inline]
    pub const fn expect(self, msg: &str) -> NonZero<Uint<LIMBS>> {
        assert!(self.is_some.is_true_vartime(), "{}", msg);
        self.value
    }
}

#[cfg(test)]
mod tests {
    use super::ConstChoice;
    use crate::Word;

    #[test]
    fn from_word_lt() {
        assert_eq!(ConstChoice::from_word_lt(4, 5), ConstChoice::TRUE);
        assert_eq!(ConstChoice::from_word_lt(5, 5), ConstChoice::FALSE);
        assert_eq!(ConstChoice::from_word_lt(6, 5), ConstChoice::FALSE);
    }

    #[test]
    fn from_word_gt() {
        assert_eq!(ConstChoice::from_word_gt(4, 5), ConstChoice::FALSE);
        assert_eq!(ConstChoice::from_word_gt(5, 5), ConstChoice::FALSE);
        assert_eq!(ConstChoice::from_word_gt(6, 5), ConstChoice::TRUE);
    }

    #[test]
    fn select() {
        let a: Word = 1;
        let b: Word = 2;
        assert_eq!(ConstChoice::TRUE.select_word(a, b), b);
        assert_eq!(ConstChoice::FALSE.select_word(a, b), a);
    }
}
