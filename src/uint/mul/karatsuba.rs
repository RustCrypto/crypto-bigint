//! Karatsuba multiplication
//!
//! This is a method which reduces the complexity of multiplication from O(n^2) to O(n^1.585).
//! For smaller numbers, it is best to stick to schoolbook multiplication, taking advantage
//! of better cache locality and avoiding recursion.
//!
//! In general, we consider the multiplication of two numbers of an equal size, `n` bits.
//! Setting b = 2^(n/2), then we can decompose the values:
//!   x•y = (x0 + x1•b)(y0 + y1•b)
//!
//! This equation is equivalent to a linear combination of three products of size `n/2`, which
//! may each be reduced by applying the same optimization.
//! Setting z0 = x0•y0, z1 = (x0-x1)(y1-y0), z2 = x1•y1:
//!   x•y = z0 + (z0 - z1 + z2)•b + z2•b^2
//!
//! Considering each sub-product as a tuple of integers `(lo, hi)`, the product is calculated as
//! follows (with appropriate carries):
//!   [z0.0, z0.0 + z0.1 - z1.0 + z2.0, z0.1 - z1.1 + z2.0 + z2.1, z2.1]
//!

use super::{uint_mul_limbs, uint_square_limbs};
use crate::{ConstChoice, Limb, Uint};

#[cfg(feature = "alloc")]
use super::square_limbs;
#[cfg(feature = "alloc")]
use crate::{WideWord, Word};

#[cfg(feature = "alloc")]
pub const KARATSUBA_MIN_STARTING_LIMBS: usize = 32;
#[cfg(feature = "alloc")]
pub const KARATSUBA_MAX_REDUCE_LIMBS: usize = 24;

/// A helper struct for performing Karatsuba multiplication on Uints.
pub(crate) struct UintKaratsubaMul<const LIMBS: usize>;

macro_rules! impl_uint_karatsuba_multiplication {
    // TODO: revisit when `const_mut_refs` is stable
    (reduce $full_size:expr, $half_size:expr) => {
        impl UintKaratsubaMul<$full_size> {
            pub(crate) const fn multiply(
                lhs: &[Limb],
                rhs: &[Limb],
            ) -> (Uint<$full_size>, Uint<$full_size>) {
                let (x0, x1) = lhs.split_at($half_size);
                let (y0, y1) = rhs.split_at($half_size);

                // Calculate z1 = (x0 - x1)(y1 - y0)
                let mut l0 = Uint::<$half_size>::ZERO;
                let mut l1 = Uint::<$half_size>::ZERO;
                let mut l0b = Limb::ZERO;
                let mut l1b = Limb::ZERO;
                let mut i = 0;
                while i < $half_size {
                    (l0.limbs[i], l0b) = x0[i].sbb(x1[i], l0b);
                    (l1.limbs[i], l1b) = y1[i].sbb(y0[i], l1b);
                    i += 1;
                }
                l0 = Uint::select(
                    &l0,
                    &l0.wrapping_neg(),
                    ConstChoice::from_word_mask(l0b.0),
                );
                l1 = Uint::select(
                    &l1,
                    &l1.wrapping_neg(),
                    ConstChoice::from_word_mask(l1b.0),
                );
                let z1 = UintKaratsubaMul::<$half_size>::multiply(&l0.limbs, &l1.limbs);
                let z1_neg = ConstChoice::from_word_mask(l0b.0)
                    .xor(ConstChoice::from_word_mask(l1b.0));

                // Conditionally add or subtract z1•b depending on its sign
                let mut res = (Uint::ZERO, z1.0, z1.1, Uint::ZERO);
                res.0 = Uint::select(&res.0, &res.0.not(), z1_neg);
                res.1 = Uint::select(&res.1, &res.1.not(), z1_neg);
                res.2 = Uint::select(&res.2, &res.2.not(), z1_neg);
                res.3 = Uint::select(&res.3, &res.3.not(), z1_neg);

                // Calculate z0 = x0•y0
                let z0 = UintKaratsubaMul::<$half_size>::multiply(&x0, &y0);
                // Calculate z2 = x1•y1
                let z2 = UintKaratsubaMul::<$half_size>::multiply(&x1, &y1);

                // Add z0 + (z0 + z2)•b + z2•b^2
                let mut carry = Limb::select(Limb::ZERO, Limb::ONE, z1_neg);
                (res.0, carry) = res.0.adc(&z0.0, carry);
                (res.1, carry) = res.1.adc(&z0.1, carry);
                let mut carry2;
                (res.1, carry2) = res.1.adc(&z0.0, Limb::ZERO);
                (res.2, carry) = res.2.adc(&z0.1, carry.wrapping_add(carry2));
                (res.1, carry2) = res.1.adc(&z2.0, Limb::ZERO);
                (res.2, carry2) = res.2.adc(&z2.1, carry2);
                carry = carry.wrapping_add(carry2);
                (res.2, carry2) = res.2.adc(&z2.0, Limb::ZERO);
                (res.3, _) = res.3.adc(&z2.1, carry.wrapping_add(carry2));

                (res.0.concat(&res.1), res.2.concat(&res.3))
            }
        }
    };
    ($small_size:expr) => {
        impl UintKaratsubaMul<$small_size> {
            #[inline]
            pub(crate) const fn multiply(lhs: &[Limb], rhs: &[Limb]) -> (Uint<$small_size>, Uint<$small_size>) {
                uint_mul_limbs(lhs, rhs)
            }
        }
    };
    ($full_size:tt, $half_size:tt $(,$rest:tt)*) => {
        impl_uint_karatsuba_multiplication!{reduce $full_size, $half_size}
        impl_uint_karatsuba_multiplication!{$half_size $(,$rest)*}
    }
}

macro_rules! impl_uint_karatsuba_squaring {
    (reduce $full_size:expr, $half_size:expr) => {
        impl UintKaratsubaMul<$full_size> {
            pub(crate) const fn square(limbs: &[Limb]) -> (Uint<$full_size>, Uint<$full_size>) {
                let (x0, x1) = limbs.split_at($half_size);
                let z0 = UintKaratsubaMul::<$half_size>::square(&x0);
                let z2 = UintKaratsubaMul::<$half_size>::square(&x1);

                // Calculate z0 + (z0 + z2)•b + z2•b^2
                let mut res = (z0.0, z0.1, Uint::<$half_size>::ZERO, Uint::<$half_size>::ZERO);
                let mut carry;
                (res.1, carry) = res.1.adc(&z0.0, Limb::ZERO);
                (res.2, carry) = z0.1.adc(&z2.0, carry);
                let mut carry2;
                (res.1, carry2) = res.1.adc(&z2.0, Limb::ZERO);
                (res.2, carry2) = res.2.adc(&z2.1, carry2);
                (res.3, _) = z2.1.adc(&Uint::ZERO, carry.wrapping_add(carry2));

                // Calculate z1 = (x0 - x1)^2
                let mut l0 = Uint::<$half_size>::ZERO;
                let mut l0b = Limb::ZERO;
                let mut i = 0;
                while i < $half_size {
                    (l0.limbs[i], l0b) = x0[i].sbb(x1[i], l0b);
                    i += 1;
                }
                l0 = Uint::select(
                    &l0,
                    &l0.wrapping_neg(),
                    ConstChoice::from_word_mask(l0b.0),
                );

                let z1 = UintKaratsubaMul::<$half_size>::square(&l0.limbs);

                // Subtract z1•b
                carry = Limb::ZERO;
                (res.1, carry) = res.1.sbb(&z1.0, carry);
                (res.2, carry) = res.2.sbb(&z1.1, carry);
                (res.3, _) = res.3.sbb(&Uint::ZERO, carry);

                (res.0.concat(&res.1), res.2.concat(&res.3))
            }
        }
    };
    ($small_size:expr) => {
        impl UintKaratsubaMul<$small_size> {
            #[inline]
            pub(crate) const fn square(limbs: &[Limb]) -> (Uint<$small_size>, Uint<$small_size>) {
                uint_square_limbs(limbs)
            }
        }
    };
    ($full_size:tt, $half_size:tt $(,$rest:tt)*) => {
        impl_uint_karatsuba_squaring!{reduce $full_size, $half_size}
        impl_uint_karatsuba_squaring!{$half_size $(,$rest)*}
    }
}

#[cfg(feature = "alloc")]
#[inline(never)]
pub(crate) fn karatsuba_mul_limbs(
    lhs: &[Limb],
    rhs: &[Limb],
    out: &mut [Limb],
    scratch: &mut [Limb],
) {
    let size = {
        let overlap = lhs.len().min(rhs.len());
        if (overlap & 1) == 1 {
            overlap.saturating_sub(1)
        } else {
            overlap
        }
    };
    if size <= KARATSUBA_MAX_REDUCE_LIMBS {
        out.fill(Limb::ZERO);
        adc_mul_limbs(lhs, rhs, out);
        return;
    }
    if lhs.len() + rhs.len() != out.len() || scratch.len() < 2 * size {
        panic!("invalid arguments to karatsuba_mul_limbs");
    }
    let half = size / 2;
    let (scratch, ext_scratch) = scratch.split_at_mut(size);

    let (x, xt) = lhs.split_at(size);
    let (y, yt) = rhs.split_at(size);
    let (x0, x1) = x.split_at(half);
    let (y0, y1) = y.split_at(half);

    // Initialize output buffer
    out.fill(Limb::ZERO);

    // Calculate abs(x0 - x1) and abs(y1 - y0)
    let mut i = 0;
    let mut borrow0 = Limb::ZERO;
    let mut borrow1 = Limb::ZERO;
    while i < half {
        (scratch[i], borrow0) = x0[i].sbb(x1[i], borrow0);
        (scratch[i + half], borrow1) = y1[i].sbb(y0[i], borrow1);
        i += 1;
    }
    // Conditionally negate terms depending whether they borrowed
    conditional_wrapping_neg_assign(&mut scratch[..half], ConstChoice::from_word_mask(borrow0.0));
    conditional_wrapping_neg_assign(
        &mut scratch[half..size],
        ConstChoice::from_word_mask(borrow1.0),
    );

    // Calculate abs(z1) = abs(x0 - x1)•abs(y1 - y0)
    karatsuba_mul_limbs(
        &scratch[..half],
        &scratch[half..size],
        &mut out[half..size + half],
        ext_scratch,
    );
    let z1_neg = ConstChoice::from_word_mask(borrow0.0).xor(ConstChoice::from_word_mask(borrow1.0));
    // Conditionally negate the output
    conditional_wrapping_neg_assign(&mut out[..2 * size], z1_neg);

    // Calculate z0 = x0•y0 into scratch
    karatsuba_mul_limbs(x0, y0, scratch, ext_scratch);
    // Add z0•(1 + b) to output
    let mut carry = Limb::ZERO;
    let mut carry2 = Limb::ZERO;
    i = 0;
    while i < size {
        (out[i], carry) = out[i].adc(scratch[i], carry); // add z0
        i += 1;
    }
    i = 0;
    while i < half {
        (out[i + half], carry2) = out[i + half].adc(scratch[i], carry2); // add z0.0
        i += 1;
    }
    carry = carry.wrapping_add(carry2);
    while i < size {
        (out[i + half], carry) = out[i + half].adc(scratch[i], carry); // add z0.1
        i += 1;
    }

    // Calculate z2 = x1•y1 into scratch
    karatsuba_mul_limbs(x1, y1, scratch, ext_scratch);
    // Add z2•(b + b^2) to output
    carry2 = Limb::ZERO;
    i = 0;
    while i < size {
        (out[i + half], carry2) = out[i + half].adc(scratch[i], carry2); // add z2
        i += 1;
    }
    carry = carry.wrapping_add(carry2);
    carry2 = Limb::ZERO;
    i = 0;
    while i < half {
        (out[i + size], carry2) = out[i + size].adc(scratch[i], carry2); // add z2.0
        i += 1;
    }
    carry = carry.wrapping_add(carry2);
    while i < size {
        (out[i + size], carry) = out[i + size].adc(scratch[i], carry); // add z2.1
        i += 1;
    }

    // Handle trailing limbs
    if !xt.is_empty() {
        adc_mul_limbs(xt, rhs, &mut out[size..]);
    }
    if !yt.is_empty() {
        let end_pos = 2 * size + yt.len();
        carry = adc_mul_limbs(yt, x, &mut out[size..end_pos]);
        i = end_pos;
        while i < out.len() {
            (out[i], carry) = out[i].adc(Limb::ZERO, carry);
            i += 1;
        }
    }
}

#[cfg(feature = "alloc")]
#[inline(never)]
pub(crate) fn karatsuba_square_limbs(limbs: &[Limb], out: &mut [Limb], scratch: &mut [Limb]) {
    let size = limbs.len();
    if size <= KARATSUBA_MAX_REDUCE_LIMBS * 2 || (size & 1) == 1 {
        out.fill(Limb::ZERO);
        square_limbs(limbs, out);
        return;
    }
    if 2 * size != out.len() || scratch.len() < out.len() {
        panic!("invalid arguments to karatsuba_square_limbs");
    }
    let half = size / 2;
    let (scratch, ext_scratch) = scratch.split_at_mut(size);
    let (x0, x1) = limbs.split_at(half);

    // Initialize output buffer
    out[..2 * size].fill(Limb::ZERO);

    // Calculate x0 - x1
    let mut i = 0;
    let mut borrow = Limb::ZERO;
    while i < half {
        (scratch[i], borrow) = x0[i].sbb(x1[i], borrow);
        i += 1;
    }
    // Conditionally negate depending whether subtraction borrowed
    conditional_wrapping_neg_assign(&mut scratch[..half], ConstChoice::from_word_mask(borrow.0));
    // Calculate z1 = (x0 - x1)^2 into output
    karatsuba_square_limbs(&scratch[..half], &mut out[half..3 * half], ext_scratch);
    // Negate the output (will add 1 to produce the wrapping negative)
    i = 0;
    while i < 2 * size {
        out[i] = !out[i];
        i += 1;
    }

    // Calculate z0 = x0^2 into scratch
    karatsuba_square_limbs(x0, scratch, ext_scratch);
    // Add z0•(1 + b) to output
    let mut carry = Limb::ONE; // add 1 to complete wrapping negative
    let mut carry2 = Limb::ZERO;
    i = 0;
    while i < size {
        (out[i], carry) = out[i].adc(scratch[i], carry); // add z0
        i += 1;
    }
    i = 0;
    while i < half {
        (out[i + half], carry2) = out[i + half].adc(scratch[i], carry2); // add z0.0
        i += 1;
    }
    carry = carry.wrapping_add(carry2);
    while i < size {
        (out[i + half], carry) = out[i + half].adc(scratch[i], carry); // add z0.1
        i += 1;
    }

    // Calculate z2 = x1^2 into scratch
    karatsuba_square_limbs(x1, scratch, ext_scratch);
    // Add z2•(b + b^2) to output
    carry2 = Limb::ZERO;
    i = 0;
    while i < size {
        (out[i + half], carry2) = out[i + half].adc(scratch[i], carry2); // add z2
        i += 1;
    }
    carry = carry.wrapping_add(carry2);
    carry2 = Limb::ZERO;
    i = 0;
    while i < half {
        (out[i + size], carry2) = out[i + size].adc(scratch[i], carry2); // add z2.0
        i += 1;
    }
    carry = carry.wrapping_add(carry2);
    while i < size {
        (out[i + size], carry) = out[i + size].adc(scratch[i], carry); // add z2.1
        i += 1;
    }
}

#[cfg(feature = "alloc")]
/// Conditionally replace the contents of a mutable limb slice with its wrapping negation.
#[inline]
fn conditional_wrapping_neg_assign(limbs: &mut [Limb], choice: ConstChoice) {
    let mut carry = choice.select_word(0, 1) as WideWord;
    let mut r;
    let mut i = 0;
    while i < limbs.len() {
        r = (choice.select_word(limbs[i].0, !limbs[i].0) as WideWord) + carry;
        limbs[i].0 = r as Word;
        carry = r >> Word::BITS;
        i += 1;
    }
}

/// Add the schoolbook product of two limb slices to a limb slice, returning the carry.
#[cfg(feature = "alloc")]
fn adc_mul_limbs(lhs: &[Limb], rhs: &[Limb], out: &mut [Limb]) -> Limb {
    if lhs.len() + rhs.len() != out.len() {
        panic!("adc_mul_limbs length mismatch");
    }

    let mut carry = Limb::ZERO;
    let mut i = 0;
    while i < lhs.len() {
        let mut j = 0;
        let mut carry2 = Limb::ZERO;
        let xi = lhs[i];

        while j < rhs.len() {
            let k = i + j;
            (out[k], carry2) = out[k].mac(xi, rhs[j], carry2);
            j += 1;
        }

        carry = carry.wrapping_add(carry2);
        (out[i + j], carry) = out[i + j].adc(Limb::ZERO, carry);
        i += 1;
    }

    carry
}

impl_uint_karatsuba_multiplication!(128, 64, 32, 16, 8);
impl_uint_karatsuba_squaring!(128, 64, 32);
