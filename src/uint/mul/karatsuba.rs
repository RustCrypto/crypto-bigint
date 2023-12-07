use core::cmp::Ordering;

use alloc::vec::Vec;

use crate::{limb::SignedWideWord, WideWord, Word};

use super::mul_limbs as mac3;

/// Karatsuba multiplication:
///
/// The idea is that we break x and y up into two smaller numbers that each have about half
/// as many digits, like so (note that multiplying by b is just a shift):
///
/// x = x0 + x1 * b
/// y = y0 + y1 * b
///
/// With some algebra, we can compute x * y with three smaller products, where the inputs to
/// each of the smaller products have only about half as many digits as x and y:
///
/// x * y = (x0 + x1 * b) * (y0 + y1 * b)
///
/// x * y = x0 * y0
///       + x0 * y1 * b
///       + x1 * y0 * b       + x1 * y1 * b^2
///
/// Let p0 = x0 * y0 and p2 = x1 * y1:
///
/// x * y = p0
///       + (x0 * y1 + x1 * y0) * b
///       + p2 * b^2
///
/// The real trick is that middle term:
///
///   x0 * y1 + x1 * y0
/// = x0 * y1 + x1 * y0 - p0 + p0 - p2 + p2
/// = x0 * y1 + x1 * y0 - x0 * y0 - x1 * y1 + p0 + p2
///
/// Now we complete the square:
///
/// = -(x0 * y0 - x0 * y1 - x1 * y0 + x1 * y1) + p0 + p2
/// = -((x1 - x0) * (y1 - y0)) + p0 + p2
///
/// Let p1 = (x1 - x0) * (y1 - y0), and substitute back into our original formula:
///
/// x * y = p0
///       + (p0 + p2 - p1) * b
///       + p2 * b^2
///
/// Where the three intermediate products are:
///
/// p0 = x0 * y0
/// p1 = (x1 - x0) * (y1 - y0)
/// p2 = x1 * y1
///
/// In doing the computation, we take great care to avoid unnecessary temporary variables
/// (since creating a BigUint requires a heap allocation): thus, we rearrange the formula a
/// bit so we can use the same temporary variable for all the intermediate products:
///
/// x * y = p2 * b^2 + p2 * b
///       + p0 * b + p0
///       - p1 * b
///
/// The other trick we use is instead of doing explicit shifts, we slice acc at the
/// appropriate offset when doing the add.
pub(super) fn mul(x: &[Word], y: &[Word], acc: &mut [Word]) {
    let b = x.len() / 2;
    let (x0, x1) = x.split_at(b);
    let (y0, y1) = y.split_at(b);

    // We reuse the same container for all the intermediate multiplies and have to size p
    // appropriately here.
    let len = x1.len() + y1.len();
    let mut p = vec![0; len];

    // p2 = x1 * y1
    mac3(x1, y1, &mut p[..]);

    add2(&mut acc[b..], &p[..]);
    add2(&mut acc[b * 2..], &p[..]);

    // Zero out p before the next multiply:
    clear(&mut p);

    // p0 = x0 * y0
    mac3(x0, y0, &mut p[..]);

    add2(&mut acc[..], &p[..]);
    add2(&mut acc[b..], &p[..]);

    // p1 = (x1 - x0) * (y1 - y0)
    // We do this one last, since it may be negative and acc can't ever be negative:
    let (j0_sign, j0) = sub_sign(x1, x0);
    let (j1_sign, j1) = sub_sign(y1, y0);

    match (j0_sign, j1_sign) {
        (Sign::Plus, Sign::Plus) | (Sign::Minus, Sign::Minus) => {
            clear(&mut p);

            mac3(&j0[..], &j1[..], &mut p[..]);
            sub2(&mut acc[b..], &p[..]);
        }
        (Sign::Minus, Sign::Plus) | (Sign::Plus, Sign::Minus) => {
            mac3(&j0[..], &j1[..], &mut acc[b..]);
        }
        (Sign::NoSign, _) | (_, Sign::NoSign) => {}
    }
}

fn clear(v: &mut [Word]) {
    for el in v {
        *el = 0;
    }
}

// TODO: fold the below in with other impls

/// Two argument addition of raw slices:
/// a += b
///
/// The caller _must_ ensure that a is big enough to store the result - typically this means
/// resizing a to max(a.len(), b.len()) + 1, to fit a possible carry.
fn add2(a: &mut [Word], b: &[Word]) {
    let carry = __add2(a, b);

    assert!(carry == 0);
}

#[inline]
fn __add2(a: &mut [Word], b: &[Word]) -> Word {
    debug_assert!(a.len() >= b.len(), "{} < {}", a.len(), b.len());

    let mut carry = 0;
    let (a_lo, a_hi) = a.split_at_mut(b.len());

    for (a, b) in a_lo.iter_mut().zip(b) {
        *a = adc(*a, *b, &mut carry);
    }

    if carry != 0 {
        for a in a_hi {
            *a = adc(*a, 0, &mut carry);
            if carry == 0 {
                break;
            }
        }
    }

    carry as Word
}

#[inline]
pub(crate) fn adc(a: Word, b: Word, acc: &mut WideWord) -> Word {
    *acc += a as WideWord;
    *acc += b as WideWord;
    let lo = *acc as Word;
    *acc >>= Word::BITS;
    lo
}

enum Sign {
    Plus,
    Minus,
    NoSign,
}

fn sub_sign(a: &[Word], b: &[Word]) -> (Sign, Vec<Word>) {
    match cmp_slice(a, b) {
        Ordering::Greater => {
            let mut a = a.to_vec();
            sub2(&mut a, b);
            (Sign::Plus, a)
        }
        Ordering::Less => {
            let mut b = b.to_vec();
            sub2(&mut b, a);
            (Sign::Minus, b)
        }
        _ => (Sign::NoSign, Vec::new()),
    }
}

/// Subtract with borrow:
#[inline]
fn sbb(a: Word, b: Word, acc: &mut SignedWideWord) -> Word {
    *acc += a as SignedWideWord;
    *acc -= b as SignedWideWord;
    let lo = *acc as Word;
    *acc >>= Word::BITS;
    lo
}

fn sub2(a: &mut [Word], b: &[Word]) {
    let mut borrow = 0;

    let len = core::cmp::min(a.len(), b.len());
    let (a_lo, a_hi) = a.split_at_mut(len);
    let (b_lo, b_hi) = b.split_at(len);

    for (a, b) in a_lo.iter_mut().zip(b_lo) {
        *a = sbb(*a, *b, &mut borrow);
    }

    if borrow != 0 {
        for a in a_hi {
            *a = sbb(*a, 0, &mut borrow);
            if borrow == 0 {
                break;
            }
        }
    }

    // note: we're _required_ to fail on underflow
    assert!(
        borrow == 0 && b_hi.iter().all(|x| *x == 0),
        "Cannot subtract b from a because b is larger than a."
    );
}

fn cmp_slice(a: &[Word], b: &[Word]) -> Ordering {
    debug_assert!(a.last() != Some(&0));
    debug_assert!(b.last() != Some(&0));

    let (a_len, b_len) = (a.len(), b.len());
    if a_len < b_len {
        return Ordering::Less;
    }
    if a_len > b_len {
        return Ordering::Greater;
    }

    for (&ai, &bi) in a.iter().rev().zip(b.iter().rev()) {
        if ai < bi {
            return Ordering::Less;
        }
        if ai > bi {
            return Ordering::Greater;
        }
    }
    Ordering::Equal
}
