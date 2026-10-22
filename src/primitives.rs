use crate::{Choice, WideWord, Word};

/// Computes `lhs + rhs + carry`, returning the result along with the new carry (0, 1, or 2).
#[inline(always)]
#[allow(clippy::cast_possible_truncation)]
pub(crate) const fn carrying_add(lhs: Word, rhs: Word, carry: Word) -> (Word, Word) {
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
pub(crate) const fn overflowing_add(lhs: Word, rhs: Word) -> (Word, Word) {
    let (res, carry) = lhs.overflowing_add(rhs);
    (res, carry as Word)
}

/// Computes `lhs + rhs`, returning the result along with the carry (0 or 1).
///
/// This avoids `WideWord::overflowing_add`, which LLVM can lower to a
/// secret-dependent branch on targets without native double-width arithmetic.
#[inline(always)]
pub(crate) const fn overflowing_add_wide(lhs: WideWord, rhs: WideWord) -> (WideWord, WideWord) {
    let result = lhs.wrapping_add(rhs);
    let carry = ((lhs & rhs) | ((lhs | rhs) & !result)) >> (WideWord::BITS - 1);
    (result, carry)
}

/// Computes `lhs - (rhs + borrow)`, returning the result along with the new borrow.
#[inline(always)]
pub(crate) const fn borrowing_sub(lhs: Word, rhs: Word, borrow: Word) -> (Word, Word) {
    let borrow = borrow >> (Word::BITS - 1);
    let ret = lhs.wrapping_sub(rhs).wrapping_sub(borrow);

    // XXX we cannot use WideWord casts here: https://github.com/rust-lang/rust/issues/149522
    // rustc 1.87 through 1.91 incorrectly optimize some WideWord bit arithmetic.
    //
    // For `ret = lhs - rhs - borrow`, the most significant bit of this expression is the borrow bit
    // which we can compute using boolean arithmetic rather than `overflowing_sub`.
    // LLVM can otherwise replace the resulting select with a secret-dependent branch.
    // Keep the bit opaque so it also cannot fold a caller's masked add-back into a branch.
    let borrow = core::hint::black_box(((!lhs & rhs) | (!(lhs ^ rhs) & ret)) >> (Word::BITS - 1));
    (ret, borrow.wrapping_neg())
}

/// Computes `value.saturating_sub(bit & 1)` without lowering to conditional control flow.
#[inline(never)]
pub(crate) const fn saturating_sub_one(value: Word, bit: Word) -> Word {
    let nonzero = (value | value.wrapping_neg()) >> (Word::BITS - 1);
    let mask = core::hint::black_box(nonzero).wrapping_neg();
    value.wrapping_sub(bit & 1) & mask
}

/// Computes `lhs * rhs`, returning the low and the high words of the result.
#[inline(always)]
#[allow(clippy::cast_possible_truncation)]
pub(crate) const fn widening_mul(lhs: Word, rhs: Word) -> (Word, Word) {
    let a = lhs as WideWord;
    let b = rhs as WideWord;
    let ret = a * b;
    (ret as Word, (ret >> Word::BITS) as Word)
}

/// Computes `(lhs * rhs) + addend + carry`, returning the result along with the new carry.
#[inline(always)]
#[allow(clippy::cast_possible_truncation)]
pub(crate) const fn carrying_mul_add(
    lhs: Word,
    rhs: Word,
    addend: Word,
    carry: Word,
) -> (Word, Word) {
    let lhs = lhs as WideWord;
    let rhs = rhs as WideWord;
    let addend = addend as WideWord;
    let carry = carry as WideWord;

    // Cannot overflow:
    // lhs      * rhs      + addend   + carry
    // (2^64-1) * (2^64-1) + (2^64-1) + (2^64-1) =
    // 2^128 - 2^65 + 1 + 2^64 - 1 + 2^64 - 1 =
    // 2^128 - 2^65 + 2*2^64 - 1 =
    // 2^128 - 1 = u128::MAX
    let ret = ((lhs * rhs) + addend) + carry;
    (ret as Word, (ret >> Word::BITS) as Word)
}

/// `const fn` equivalent of `u32::max(a, b)`.
#[inline(never)]
pub(crate) const fn u32_max(a: u32, b: u32) -> u32 {
    Choice::from_u32_lt(a, b).select_u32(a, b)
}

/// `const` equivalent of `u32::min(a, b)`.
#[inline(never)]
pub(crate) const fn u32_min(a: u32, b: u32) -> u32 {
    Choice::from_u32_lt(a, b).select_u32(b, a)
}

/// Remainder calculation, constant time for a given divisor `d`.
/// Based on "Faster Remainder by Direct Computation: Applications to Compilers and Software Libraries"
/// by Daniel Lemire, Owen Kaser, and Nathan Kurz., Fig. 1.
#[inline(never)]
#[allow(clippy::cast_possible_truncation, reason = "needs triage")]
#[allow(clippy::integer_division_remainder_used, reason = "needs triage")]
pub(crate) const fn u32_rem(n: u32, d: u32) -> u32 {
    assert!(d > 0, "divisor must be nonzero");
    let c = u64::MAX / (d as u64) + 1;
    (((c.wrapping_mul(n as u64) as u128) * d as u128) >> 64) as u32
}

/// Compute the number of bits needed to represent `n`.
#[inline(always)]
pub(crate) const fn u32_bits(n: u32) -> u32 {
    u32::BITS - n.leading_zeros()
}

/// Return a `Choice` representing whether `a < b`.
#[allow(clippy::cast_possible_truncation)]
#[cfg(target_pointer_width = "32")]
#[inline]
pub(crate) const fn usize_lt(a: usize, b: usize) -> Choice {
    Choice::from_u32_lt(a as u32, b as u32)
}

/// Return a `Choice` representing whether `a < b`.
#[allow(clippy::cast_possible_truncation)]
#[cfg(target_pointer_width = "64")]
#[inline]
pub(crate) const fn usize_lt(a: usize, b: usize) -> Choice {
    Choice::from_u64_lt(a as u64, b as u64)
}

cpubits::cpubits! {
    32 => {
        /// Returns the multiplicative inverse of the argument modulo 2^32.
        ///
        /// For correct results, the input `value` must be odd.
        #[must_use]
        pub(crate) const fn u32_invert_odd(value: u32) -> u32 {
            debug_assert!(value & 1 == 1, "value must be odd");
            let x = value.wrapping_mul(3) ^ 2;
            let y = 1u32.wrapping_sub(x.wrapping_mul(value));
            let (x, y) = (x.wrapping_mul(y.wrapping_add(1)), y.wrapping_mul(y));
            let (x, y) = (x.wrapping_mul(y.wrapping_add(1)), y.wrapping_mul(y));
            x.wrapping_mul(y.wrapping_add(1))
        }
    }
}

/// Returns the multiplicative inverse of the argument modulo 2^64. The implementation is based
/// on Hurchalla's method for computing the multiplicative inverse modulo a power of two, and
/// is essentially an optimized Newton iteration.
///
/// For correct results, the input `value` must be odd.
///
/// For better understanding the implementation, the following paper is recommended:
/// J. Hurchalla, "An Improved Integer Multiplicative Inverse (modulo 2^w)",
/// <https://arxiv.org/abs/2204.04342>
#[must_use]
pub(crate) const fn u64_invert_odd(value: u64) -> u64 {
    debug_assert!(value & 1 == 1, "value must be odd");
    let x = value.wrapping_mul(3) ^ 2;
    let y = 1u64.wrapping_sub(x.wrapping_mul(value));
    let (x, y) = (x.wrapping_mul(y.wrapping_add(1)), y.wrapping_mul(y));
    let (x, y) = (x.wrapping_mul(y.wrapping_add(1)), y.wrapping_mul(y));
    let (x, y) = (x.wrapping_mul(y.wrapping_add(1)), y.wrapping_mul(y));
    x.wrapping_mul(y.wrapping_add(1))
}

#[cfg(test)]
mod tests {
    use super::{
        borrowing_sub, overflowing_add_wide, saturating_sub_one, u32_max, u32_min, u32_rem,
        usize_lt,
    };
    use crate::{WideWord, Word};

    #[test]
    fn carrying_mul_add_cannot_overflow() {
        let lhs = Word::MAX;
        let rhs = Word::MAX;
        let addend = Word::MAX;
        let carry_in = Word::MAX;
        let (result, carry_out) = super::carrying_mul_add(lhs, rhs, addend, carry_in);
        assert_eq!(result, Word::MAX);
        assert_eq!(carry_out, Word::MAX);
    }

    #[test]
    fn test_overflowing_add_wide() {
        let msb = 1 << (WideWord::BITS - 1);
        let values = [
            0,
            1,
            2,
            msb - 1,
            msb,
            msb + 1,
            WideWord::MAX - 1,
            WideWord::MAX,
        ];

        for lhs in values {
            for rhs in values {
                let (expected, carry) = lhs.overflowing_add(rhs);
                assert_eq!(
                    overflowing_add_wide(lhs, rhs),
                    (expected, WideWord::from(carry))
                );
            }
        }
    }

    #[test]
    fn test_borrowing_sub() {
        let msb = 1 << (Word::BITS - 1);
        let values = [0, 1, 2, msb - 1, msb, msb + 1, Word::MAX - 1, Word::MAX];
        let borrows = [0, 1, msb, Word::MAX];

        for &lhs in &values {
            for &rhs in &values {
                for &borrow in &borrows {
                    let (ret, borrow1) = lhs.overflowing_sub(borrow >> (Word::BITS - 1));
                    let (expected, borrow2) = ret.overflowing_sub(rhs);
                    let expected_borrow = Word::MIN.wrapping_sub(Word::from(borrow1 | borrow2));

                    assert_eq!(
                        borrowing_sub(lhs, rhs, borrow),
                        (expected, expected_borrow),
                        "lhs={lhs:#x}, rhs={rhs:#x}, borrow={borrow:#x}"
                    );
                }
            }
        }
    }

    #[test]
    fn test_saturating_sub_one() {
        for value in [0, 1, 2, Word::MAX - 1, Word::MAX] {
            for bit in [0, 1, Word::MAX] {
                assert_eq!(
                    saturating_sub_one(value, bit),
                    value.saturating_sub(bit & 1)
                );
            }
        }
    }

    #[test]
    fn test_u32_const_min() {
        assert_eq!(u32_min(0, 5), 0);
        assert_eq!(u32_min(7, 0), 0);
        assert_eq!(u32_min(7, 5), 5);
        assert_eq!(u32_min(7, 7), 7);
    }

    #[test]
    fn test_u32_const_max() {
        assert_eq!(u32_max(0, 5), 5);
        assert_eq!(u32_max(7, 0), 7);
        assert_eq!(u32_max(7, 5), 7);
        assert_eq!(u32_max(7, 7), 7);
    }

    #[test]
    fn test_u32_const_rem() {
        assert_eq!(u32_rem(0, 5), 0);
        assert_eq!(u32_rem(4, 5), 4);
        assert_eq!(u32_rem(7, 5), 2);
        assert_eq!(u32_rem(101, 5), 1);
    }

    #[test]
    fn test_usize_const_lt() {
        assert!(usize_lt(0, 5).to_bool());
        assert!(!usize_lt(7, 0).to_bool());
        assert!(!usize_lt(7, 5).to_bool());
        assert!(!usize_lt(7, 7).to_bool());
    }

    cpubits::cpubits! {
        32 => {
            #[test]
            fn test_u32_invert_odd() {
                use super::u32_invert_odd;

                assert_eq!(u32_invert_odd(1), 1);
                assert_eq!(u32_invert_odd(5).wrapping_mul(5), 1);
                assert_eq!(u32_invert_odd(u32::MAX).wrapping_mul(u32::MAX), 1);
            }
        }
    }
}
