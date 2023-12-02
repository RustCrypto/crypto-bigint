use subtle::Choice;

use crate::Word;

/// A boolean value returned by constant-time `const fn`s.
// TODO: should be replaced by `subtle::Choice` or `CtOption`
// when `subtle` starts supporting const fns.
#[derive(Debug, Copy, Clone)]
pub struct CtChoice(Word);

impl CtChoice {
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
        let bit = (((!x) & y) | (((!x) | y) & (x.wrapping_sub(y)))) >> (Word::BITS - 1);
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
        self.0 == CtChoice::TRUE.0
    }

    #[inline]
    pub(crate) const fn to_u8(self) -> u8 {
        (self.0 as u8) & 1
    }
}

impl From<CtChoice> for Choice {
    fn from(choice: CtChoice) -> Self {
        Choice::from(choice.to_u8())
    }
}

impl From<CtChoice> for bool {
    fn from(choice: CtChoice) -> Self {
        choice.is_true_vartime()
    }
}

#[cfg(test)]
mod tests {
    use super::CtChoice;
    use crate::Word;

    #[test]
    fn select() {
        let a: Word = 1;
        let b: Word = 2;
        assert_eq!(CtChoice::TRUE.select_word(a, b), b);
        assert_eq!(CtChoice::FALSE.select_word(a, b), a);
    }
}
