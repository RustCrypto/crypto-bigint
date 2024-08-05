use crate::{WideWord, Word};

/// Multiplies `x` and `y`, returning the most significant
/// and the least significant words as `(hi, lo)`.
#[inline(always)]
pub(crate) const fn mulhilo(x: Word, y: Word) -> (Word, Word) {
    let res = (x as WideWord) * (y as WideWord);
    ((res >> Word::BITS) as Word, res as Word)
}

/// Adds wide numbers represented by pairs of (most significant word, least significant word)
/// and returns the result in the same format `(hi, lo)`.
#[inline(always)]
pub(crate) const fn addhilo(x_hi: Word, x_lo: Word, y_hi: Word, y_lo: Word) -> (Word, Word) {
    let res = (((x_hi as WideWord) << Word::BITS) | (x_lo as WideWord))
        + (((y_hi as WideWord) << Word::BITS) | (y_lo as WideWord));
    ((res >> Word::BITS) as Word, res as Word)
}

/// Computes `lhs + rhs + carry`, returning the result along with the new carry (0, 1, or 2).
#[inline(always)]
pub const fn adc(lhs: Word, rhs: Word, carry: Word) -> (Word, Word) {
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

/// Computes `self - (rhs + borrow)`, returning the result along with the new borrow.
#[inline(always)]
pub const fn sbb(lhs: Word, rhs: Word, borrow: Word) -> (Word, Word) {
    let a = lhs as WideWord;
    let b = rhs as WideWord;
    let borrow = (borrow >> (Word::BITS - 1)) as WideWord;
    let ret = a.wrapping_sub(b + borrow);
    (ret as Word, (ret >> Word::BITS) as Word)
}

/// Computes `lhs * rhs`, returning the low and the high words of the result.
#[inline(always)]
pub const fn mul_wide(lhs: Word, rhs: Word) -> (Word, Word) {
    let a = lhs as WideWord;
    let b = rhs as WideWord;
    let ret = a * b;
    (ret as Word, (ret >> Word::BITS) as Word)
}

/// Computes `a + (b * c) + carry`, returning the result along with the new carry.
#[inline(always)]
pub(crate) const fn mac(a: Word, b: Word, c: Word, carry: Word) -> (Word, Word) {
    let a = a as WideWord;
    let b = b as WideWord;
    let c = c as WideWord;
    let carry = carry as WideWord;
    let ret = a + (b * c) + carry;
    (ret as Word, (ret >> Word::BITS) as Word)
}
