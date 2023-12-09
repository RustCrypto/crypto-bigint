use crate::{WideWord, Word};

/// Divide a two digit numerator by a one digit divisor, returns quotient and remainder:
///
/// Note: the caller must ensure that both the quotient and remainder will fit into a single digit.
/// This is _not_ true for an arbitrary numerator/denominator.
///
/// (This function also matches what the x86 divide instruction does).
#[inline]
pub(crate) fn div_wide(hi: Word, lo: Word, divisor: Word) -> (Word, Word) {
    debug_assert!(hi < divisor);

    let lhs = WideWord::from(lo) | (WideWord::from(hi) << Word::BITS);
    let rhs = divisor as WideWord;
    ((lhs / rhs) as Word, (lhs % rhs) as Word)
}
