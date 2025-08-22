use crate::Limb;

/// Schoolbook multiplication a.k.a. long multiplication, i.e. the traditional method taught in
/// schools.
///
/// The most efficient method for small numbers.
#[inline(always)]
pub const fn mul_wide(lhs: &[Limb], rhs: &[Limb], lo: &mut [Limb], hi: &mut [Limb]) {
    assert!(
        lhs.len() == lo.len() && rhs.len() == hi.len(),
        "schoolbook multiplication length mismatch"
    );

    let mut i = 0;

    while i < lhs.len() {
        let mut carry = Limb::ZERO;
        let xi = lhs[i];
        let mut j = 0;

        while j < rhs.len() {
            let k = i + j;

            if k >= lhs.len() {
                (hi[k - lhs.len()], carry) = xi.carrying_mul_add(rhs[j], hi[k - lhs.len()], carry);
            } else {
                (lo[k], carry) = xi.carrying_mul_add(rhs[j], lo[k], carry);
            }

            j += 1;
        }

        if i + j >= lhs.len() {
            hi[i + j - lhs.len()] = carry;
        } else {
            lo[i + j] = carry;
        }
        i += 1;
    }
}

/// Add the schoolbook product of two limb slices to a limb slice, returning the carry.
#[inline]
pub const fn carrying_add_mul(lhs: &[Limb], rhs: &[Limb], out: &mut [Limb]) -> Limb {
    assert!(
        lhs.len() + rhs.len() == out.len(),
        "carrying_add_mul length mismatch"
    );

    let mut carry = Limb::ZERO;
    let mut i = 0;

    while i < lhs.len() {
        let mut carry2 = Limb::ZERO;
        let xi = lhs[i];
        let mut j = 0;

        while j < rhs.len() {
            let k = i + j;
            (out[k], carry2) = xi.carrying_mul_add(rhs[j], out[k], carry2);
            j += 1;
        }

        carry = carry.wrapping_add(carry2);
        (out[i + j], carry) = out[i + j].carrying_add(Limb::ZERO, carry);
        i += 1;
    }

    carry
}

/// Schoolbook multiplication which only calculates the lower limbs of the product.
#[inline(always)]
pub const fn wrapping_mul(lhs: &[Limb], rhs: &[Limb], out: &mut [Limb]) {
    assert!(
        lhs.len() == out.len(),
        "wrapping schoolbook multiplication length mismatch"
    );

    let mut i = 0;

    while i < lhs.len() {
        let mut carry = Limb::ZERO;
        let xi = lhs[i];
        let mut j = 0;
        let mut k;

        loop {
            k = i + j;
            if j == rhs.len() || k == lhs.len() {
                break;
            }
            (out[k], carry) = xi.carrying_mul_add(rhs[j], out[k], carry);
            j += 1;
        }

        if k < lhs.len() {
            out[k] = carry;
        }
        i += 1;
    }
}

/// Schoolbook method of squaring.
///
/// Like schoolbook multiplication, but only considering half of the multiplication grid.
#[inline(always)]
pub const fn square_wide(limbs: &[Limb], lo: &mut [Limb], hi: &mut [Limb]) {
    // Translated from https://github.com/ucbrise/jedi-pairing/blob/c4bf151/include/core/bigint.hpp#L410
    //
    // Permission to relicense the resulting translation as Apache 2.0 + MIT was given
    // by the original author Sam Kumar: https://github.com/RustCrypto/crypto-bigint/pull/133#discussion_r1056870411

    assert!(
        limbs.len() == lo.len() && lo.len() == hi.len(),
        "schoolbook squaring length mismatch"
    );

    let mut i = 1;
    while i < limbs.len() {
        let mut j = 0;
        let mut carry = Limb::ZERO;
        let xi = limbs[i];

        while j < i {
            let k = i + j;

            if k >= limbs.len() {
                (hi[k - limbs.len()], carry) =
                    xi.carrying_mul_add(limbs[j], hi[k - limbs.len()], carry);
            } else {
                (lo[k], carry) = xi.carrying_mul_add(limbs[j], lo[k], carry);
            }

            j += 1;
        }

        if (2 * i) < limbs.len() {
            lo[2 * i] = carry;
        } else {
            hi[2 * i - limbs.len()] = carry;
        }

        i += 1;
    }

    // Double the current result, this accounts for the other half of the multiplication grid.
    // The top word is empty, so we use a special purpose shl.
    let mut carry = Limb::ZERO;
    let mut i = 0;
    while i < limbs.len() {
        (lo[i].0, carry) = ((lo[i].0 << 1) | carry.0, lo[i].shr(Limb::BITS - 1));
        i += 1;
    }

    let mut i = 0;
    while i < limbs.len() - 1 {
        (hi[i].0, carry) = ((hi[i].0 << 1) | carry.0, hi[i].shr(Limb::BITS - 1));
        i += 1;
    }
    hi[limbs.len() - 1] = carry;

    // Handle the diagonal of the multiplication grid, which finishes the multiplication grid.
    let mut carry = Limb::ZERO;
    let mut i = 0;
    while i < limbs.len() {
        let xi = limbs[i];
        if (i * 2) < limbs.len() {
            (lo[i * 2], carry) = xi.carrying_mul_add(xi, lo[i * 2], carry);
        } else {
            (hi[i * 2 - limbs.len()], carry) =
                xi.carrying_mul_add(xi, hi[i * 2 - limbs.len()], carry);
        }

        if (i * 2 + 1) < limbs.len() {
            (lo[i * 2 + 1], carry) = lo[i * 2 + 1].overflowing_add(carry);
        } else {
            (hi[i * 2 + 1 - limbs.len()], carry) =
                hi[i * 2 + 1 - limbs.len()].overflowing_add(carry);
        }

        i += 1;
    }
}
