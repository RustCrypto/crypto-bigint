//! `Word` represents the core integer type we use as the core of `Limb`, and is typically the same
//! size as a pointer on a particular CPU.

use crate::ConstChoice;

#[cfg(not(any(target_pointer_width = "32", target_pointer_width = "64")))]
compile_error!("this crate builds on 32-bit and 64-bit platforms only");

//
// 32-bit definitions
//

/// Inner integer type that the [`Limb`] newtype wraps.
#[cfg(target_pointer_width = "32")]
pub type Word = u32;

/// Unsigned wide integer type: double the width of [`Word`].
#[cfg(target_pointer_width = "32")]
pub type WideWord = u64;

//
// 64-bit definitions
//

/// Unsigned integer type that the [`Limb`][`crate::Limb`] newtype wraps.
#[cfg(target_pointer_width = "64")]
pub type Word = u64;

/// Wide integer type: double the width of [`Word`].
#[cfg(target_pointer_width = "64")]
pub type WideWord = u128;

/// Returns the truthy value if `x == y`, and the falsy value otherwise.
#[inline]
pub(crate) const fn from_word_eq(x: Word, y: Word) -> ConstChoice {
    from_word_nonzero(x ^ y).not()
}

/// Returns the truthy value if `x > y`, and the falsy value otherwise.
#[inline]
pub(crate) const fn from_word_gt(x: Word, y: Word) -> ConstChoice {
    from_word_lt(y, x)
}

/// Returns the truthy value if `x <= y` and the falsy value otherwise.
#[inline]
pub(crate) const fn from_word_le(x: Word, y: Word) -> ConstChoice {
    // See "Hacker's Delight" 2nd ed, section 2-12 (Comparison predicates)
    let bit = (((!x) | y) & ((x ^ y) | !(y.wrapping_sub(x)))) >> (Word::BITS - 1);
    from_word_lsb(bit)
}

/// Returns the truthy value if `value == 1`, and the falsy value if `value == 0`.
/// Panics for other values.
#[inline]
pub(crate) const fn from_word_lsb(value: Word) -> ConstChoice {
    ConstChoice::new((value & 1) as u8)
}

/// Returns the truthy value if `x < y`, and the falsy value otherwise.
#[inline]
pub(crate) const fn from_word_lt(x: Word, y: Word) -> ConstChoice {
    // See "Hacker's Delight" 2nd ed, section 2-12 (Comparison predicates)
    let bit = (((!x) & y) | (((!x) | y) & (x.wrapping_sub(y)))) >> (Word::BITS - 1);
    from_word_lsb(bit)
}

/// Returns the truthy value if `value == Word::MAX`, and the falsy value if `value == 0`.
/// Panics for other values.
#[inline]
pub(crate) const fn from_word_mask(value: Word) -> ConstChoice {
    from_word_eq(value, Word::MAX)
}

/// Returns the truthy value if the most significant bit of `value` is `1`,
/// and the falsy value if it equals `0`.
#[inline]
pub(crate) const fn from_word_msb(value: Word) -> ConstChoice {
    from_word_lsb(value >> (Word::BITS - 1))
}

/// Returns the truthy value if `value != 0`, and the falsy value otherwise.
#[inline]
pub(crate) const fn from_word_nonzero(value: Word) -> ConstChoice {
    from_word_lsb((value | value.wrapping_neg()) >> (Word::BITS - 1))
}

/// Returns the truthy value if `x <= y` and the falsy value otherwise.
#[inline]
pub(crate) const fn from_wide_word_le(x: WideWord, y: WideWord) -> ConstChoice {
    // See "Hacker's Delight" 2nd ed, section 2-12 (Comparison predicates)
    let bit = (((!x) | y) & ((x ^ y) | !(y.wrapping_sub(x)))) >> (WideWord::BITS - 1);
    from_wide_word_lsb(bit)
}

/// Returns the truthy value if `value == 1`, and the falsy value if `value == 0`.
/// Panics for other values.
#[inline]
pub(crate) const fn from_wide_word_lsb(value: WideWord) -> ConstChoice {
    ConstChoice::new((value & 1) as u8)
}

/// Return `b` if `self` is truthy, otherwise return `a`.
#[inline]
pub(crate) const fn select_word(choice: ConstChoice, a: Word, b: Word) -> Word {
    a ^ (choice_to_word_mask(choice) & (a ^ b))
}

/// Return `b` if `self` is truthy, otherwise return `a`.
#[inline]
pub(crate) const fn select_wide_word(choice: ConstChoice, a: WideWord, b: WideWord) -> WideWord {
    a ^ (choice_to_wide_word_mask(choice) & (a ^ b))
}

/// Create a `Word`-sized bitmask.
///
/// # Returns
/// - `0` for `ConstChoice::FALSE`
/// - `Word::MAX` for `ConstChoice::TRUE`
#[inline]
pub(crate) const fn choice_to_word_mask(choice: ConstChoice) -> Word {
    (choice.to_u8_vartime() as Word).wrapping_neg()
}

/// Create a `WideWord`-sized bitmask.
///
/// # Returns
/// - `0` for `ConstChoice::FALSE`
/// - `Word::MAX` for `ConstChoice::TRUE`
#[inline]
pub(crate) const fn choice_to_wide_word_mask(choice: ConstChoice) -> WideWord {
    (choice.to_u8_vartime() as WideWord).wrapping_neg()
}

#[cfg(test)]
mod tests {
    use crate::{ConstChoice, WideWord, Word};

    #[test]
    fn from_word_lt() {
        assert_eq!(super::from_word_lt(4, 5), ConstChoice::TRUE);
        assert_eq!(super::from_word_lt(5, 5), ConstChoice::FALSE);
        assert_eq!(super::from_word_lt(6, 5), ConstChoice::FALSE);
    }

    #[test]
    fn from_word_gt() {
        assert_eq!(super::from_word_gt(4, 5), ConstChoice::FALSE);
        assert_eq!(super::from_word_gt(5, 5), ConstChoice::FALSE);
        assert_eq!(super::from_word_gt(6, 5), ConstChoice::TRUE);
    }

    #[test]
    fn from_wide_word_le() {
        assert_eq!(super::from_wide_word_le(4, 5), ConstChoice::TRUE);
        assert_eq!(super::from_wide_word_le(5, 5), ConstChoice::TRUE);
        assert_eq!(super::from_wide_word_le(6, 5), ConstChoice::FALSE);
    }

    #[test]
    fn select_word() {
        let a: Word = 1;
        let b: Word = 2;
        assert_eq!(super::select_word(ConstChoice::TRUE, a, b), b);
        assert_eq!(super::select_word(ConstChoice::FALSE, a, b), a);
    }

    #[test]
    fn select_wide_word() {
        let a: WideWord = (1 << Word::BITS) + 1;
        let b: WideWord = (3 << Word::BITS) + 4;
        assert_eq!(super::select_wide_word(ConstChoice::TRUE, a, b), b);
        assert_eq!(super::select_wide_word(ConstChoice::FALSE, a, b), a);
    }
}
