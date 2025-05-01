use crate::{WideWord, Word};

/// Adds wide numbers represented by pairs of (least significant word, most significant word)
/// and returns the result in the same format `(lo, hi)`.
#[inline(always)]
pub(crate) const fn addhilo(x_lo: Word, x_hi: Word, y_lo: Word, y_hi: Word) -> (Word, Word) {
    let res = (((x_hi as WideWord) << Word::BITS) | (x_lo as WideWord))
        + (((y_hi as WideWord) << Word::BITS) | (y_lo as WideWord));
    (res as Word, (res >> Word::BITS) as Word)
}

/// Computes `lhs + rhs + carry`, returning the result along with the new carry (0, 1, or 2).
#[inline(always)]
pub const fn carrying_add(lhs: Word, rhs: Word, carry: Word) -> (Word, Word) {
    // We could use `Word::overflowing_add()` here analogous to `overflowing_add()`,
    // but this version seems to produce a slightly better assembly.
    let a = lhs as WideWord;
    let b = rhs as WideWord;
    let carry = carry as WideWord;
    let ret = a + b + carry;
    (ret as Word, (ret >> Word::BITS) as Word)
}

/// Computes `lhs + rhs`, returning the result along with the carry (0 or 1).
#[inline(always)]
pub const fn overflowing_add(lhs: Word, rhs: Word) -> (Word, Word) {
    let (res, carry) = lhs.overflowing_add(rhs);
    (res, carry as Word)
}

/// Computes `lhs - (rhs + borrow)`, returning the result along with the new borrow.
#[inline(always)]
pub const fn borrowing_sub(lhs: Word, rhs: Word, borrow: Word) -> (Word, Word) {
    let a = lhs as WideWord;
    let b = rhs as WideWord;
    let borrow = (borrow >> (Word::BITS - 1)) as WideWord;
    let ret = a.wrapping_sub(b + borrow);
    (ret as Word, (ret >> Word::BITS) as Word)
}

/// Computes `lhs * rhs`, returning the low and the high words of the result.
#[inline(always)]
pub const fn widening_mul(lhs: Word, rhs: Word) -> (Word, Word) {
    let a = lhs as WideWord;
    let b = rhs as WideWord;
    let ret = a * b;
    (ret as Word, (ret >> Word::BITS) as Word)
}

/// Computes `(lhs * rhs) + addend + carry`, returning the result along with the new carry.
#[inline(always)]
pub(crate) const fn carrying_mul_add(
    lhs: Word,
    rhs: Word,
    addend: Word,
    carry: Word,
) -> (Word, Word) {
    let lhs = lhs as WideWord;
    let rhs = rhs as WideWord;
    let addend = addend as WideWord;
    let ret = (lhs * rhs) + addend;
    let (lo, hi) = (ret as Word, (ret >> Word::BITS) as Word);

    let (lo, c) = lo.overflowing_add(carry);

    // Even if all the arguments are `Word::MAX` we can't overflow `hi`.
    let hi = hi.wrapping_add(c as Word);

    (lo, hi)
}
