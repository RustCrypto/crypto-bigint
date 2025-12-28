//! `Word` represents the core integer type we use as the core of `Limb`, and is typically the same
//! size as a pointer on a particular CPU.

use ctutils::Choice;

#[cfg(not(any(target_pointer_width = "32", target_pointer_width = "64")))]
compile_error!("this crate builds on 32-bit and 64-bit platforms only");

/// 32-bit definitions
#[cfg(target_pointer_width = "32")]
mod word32 {
    use super::Choice;

    /// Inner integer type that the [`Limb`] newtype wraps.
    pub type Word = u32;

    /// Unsigned wide integer type: double the width of [`Word`].
    pub type WideWord = u64;

    /// Returns the truthy value if `x <= y` and the falsy value otherwise.
    #[inline]
    pub(crate) const fn choice_from_le(x: Word, y: Word) -> Choice {
        Choice::from_u32_le(x, y)
    }

    /// Returns the truthy value if `x < y`, and the falsy value otherwise.
    #[inline]
    pub(crate) const fn choice_from_lt(x: Word, y: Word) -> Choice {
        Choice::from_u32_lt(x, y)
    }

    /// Returns the truthy value if `x <= y` and the falsy value otherwise.
    #[inline]
    pub(crate) const fn choice_from_wide_le(x: WideWord, y: WideWord) -> Choice {
        Choice::from_u64_le(x, y)
    }
}

/// 64-bit definitions
#[cfg(target_pointer_width = "64")]
mod word64 {
    use super::Choice;

    /// Unsigned integer type that the [`Limb`][`crate::Limb`] newtype wraps.
    pub type Word = u64;

    /// Wide integer type: double the width of [`Word`].
    pub type WideWord = u128;

    /// Returns the truthy value if `x <= y` and the falsy value otherwise.
    #[inline]
    pub(crate) const fn choice_from_le(x: Word, y: Word) -> Choice {
        Choice::from_u64_le(x, y)
    }

    /// Returns the truthy value if `x < y`, and the falsy value otherwise.
    #[inline]
    pub(crate) const fn choice_from_lt(x: Word, y: Word) -> Choice {
        Choice::from_u64_lt(x, y)
    }

    /// Returns the truthy value if `x <= y` and the falsy value otherwise.
    #[inline]
    pub(crate) const fn choice_from_wide_le(x: WideWord, y: WideWord) -> Choice {
        Choice::from_u128_le(x, y)
    }
}

#[cfg(target_pointer_width = "32")]
pub use word32::*;
#[cfg(target_pointer_width = "64")]
pub use word64::*;

/// Returns the truthy value if `x == y`, and the falsy value otherwise.
#[inline]
pub(crate) const fn choice_from_eq(x: Word, y: Word) -> Choice {
    choice_from_nz(x ^ y).not()
}

/// Returns the truthy value if `x > y`, and the falsy value otherwise.
#[inline]
pub(crate) const fn choice_from_gt(x: Word, y: Word) -> Choice {
    choice_from_lt(y, x)
}

/// Returns the truthy value if `value == 1`, and the falsy value if `value == 0`.
#[inline]
pub(crate) const fn choice_from_lsb(value: Word) -> Choice {
    Choice::new((value & 1) as u8)
}

/// Returns the truthy value if `value == Word::MAX`, and the falsy value if `value == 0`.
#[inline]
pub(crate) const fn choice_from_mask(value: Word) -> Choice {
    choice_from_eq(value, Word::MAX)
}

/// Returns the truthy value if the most significant bit of `value` is `1`,
/// and the falsy value if it equals `0`.
#[inline]
pub(crate) const fn choice_from_msb(value: Word) -> Choice {
    choice_from_lsb(value >> (Word::BITS - 1))
}

/// Returns the truthy value if `value != 0`, and the falsy value otherwise.
#[inline]
pub(crate) const fn choice_from_nz(value: Word) -> Choice {
    choice_from_lsb((value | value.wrapping_neg()) >> (Word::BITS - 1))
}

/// Return `b` if `self` is truthy, otherwise return `a`.
#[inline]
pub(crate) const fn select(a: Word, b: Word, choice: Choice) -> Word {
    a ^ (choice_to_mask(choice) & (a ^ b))
}

/// Return `b` if `self` is truthy, otherwise return `a`.
#[inline]
pub(crate) const fn select_wide(a: WideWord, b: WideWord, choice: Choice) -> WideWord {
    a ^ (choice_to_wide_mask(choice) & (a ^ b))
}

/// Create a `Word`-sized bitmask.
///
/// # Returns
/// - `0` for `Choice::FALSE`
/// - `Word::MAX` for `Choice::TRUE`
#[inline]
pub(crate) const fn choice_to_mask(choice: Choice) -> Word {
    (choice.to_u8_vartime() as Word).wrapping_neg()
}

/// Create a `WideWord`-sized bitmask.
///
/// # Returns
/// - `0` for `Choice::FALSE`
/// - `Word::MAX` for `Choice::TRUE`
#[inline]
pub(crate) const fn choice_to_wide_mask(choice: Choice) -> WideWord {
    (choice.to_u8_vartime() as WideWord).wrapping_neg()
}

#[cfg(test)]
mod tests {
    use super::{Choice, WideWord, Word};

    #[test]
    fn choice_from_lt() {
        assert_eq!(super::choice_from_lt(4, 5), Choice::TRUE);
        assert_eq!(super::choice_from_lt(5, 5), Choice::FALSE);
        assert_eq!(super::choice_from_lt(6, 5), Choice::FALSE);
    }

    #[test]
    fn choice_from_gt() {
        assert_eq!(super::choice_from_gt(4, 5), Choice::FALSE);
        assert_eq!(super::choice_from_gt(5, 5), Choice::FALSE);
        assert_eq!(super::choice_from_gt(6, 5), Choice::TRUE);
    }

    #[test]
    fn choice_from_wide_le() {
        assert_eq!(super::choice_from_wide_le(4, 5), Choice::TRUE);
        assert_eq!(super::choice_from_wide_le(5, 5), Choice::TRUE);
        assert_eq!(super::choice_from_wide_le(6, 5), Choice::FALSE);
    }

    #[test]
    fn select() {
        let a: Word = 1;
        let b: Word = 2;
        assert_eq!(super::select(a, b, Choice::FALSE), a);
        assert_eq!(super::select(a, b, Choice::TRUE), b);
    }

    #[test]
    fn select_wide() {
        let a: WideWord = (1 << Word::BITS) + 1;
        let b: WideWord = (3 << Word::BITS) + 4;
        assert_eq!(super::select_wide(a, b, Choice::FALSE), a);
        assert_eq!(super::select_wide(a, b, Choice::TRUE), b);
    }
}
