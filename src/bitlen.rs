//! Bit calculations.
//!
//! These provide a single place to handle bits-to-bytes conversions and the `u32`/`usize`
//! discrepancy that can only be solved by panics or casting.

use crate::Limb;

/// Calculate a `u32` representing a number of bits from the given number of bytes as a `usize`.
#[cfg_attr(not(feature = "alloc"), allow(dead_code))]
#[inline(always)]
pub(crate) const fn from_bytes(nbytes: usize) -> u32 {
    mul(nbytes, 8)
}

/// Calculate a `u32` representing a number of bits in an integer with the given number of limbs.
#[inline(always)]
pub(crate) const fn from_limbs(nlimbs: usize) -> u32 {
    mul(nlimbs, Limb::BITS)
}

/// Calculate a `usize` representing the number of bytes required to store the given number of bits
/// represented as a `u32` (i.e. rounding up).
#[cfg_attr(not(feature = "alloc"), allow(dead_code))]
#[inline(always)]
pub(crate) const fn to_bytes(nbits: u32) -> usize {
    u32_to_usize(nbits.div_ceil(8))
}

/// Calculate a `usize` representing the number of limbs required to store the given number of bits
/// represented as a `u32` (i.e. rounding up).
#[inline(always)]
pub(crate) const fn to_limbs(nbits: u32) -> usize {
    u32_to_usize(nbits.div_ceil(Limb::BITS))
}

#[inline(always)]
const fn u32_to_usize(n: u32) -> usize {
    const {
        // Ensure cast from `u32` to `usize` won't overflow
        assert!(usize::BITS >= u32::BITS, "usize too small");
    }

    n as usize
}

#[allow(
    clippy::cast_possible_truncation,
    reason = "assertion ensures panic instead of truncation"
)]
#[inline(always)]
const fn usize_to_u32(n: usize) -> u32 {
    debug_assert!(n < u32_to_usize(u32::MAX), "u32 overflow");
    n as u32
}

#[inline(always)]
const fn mul(size: usize, n: u32) -> u32 {
    if cfg!(debug_assertions) {
        usize_to_u32(size).checked_mul(n).expect("u32 overflow")
    } else {
        usize_to_u32(size) * n
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn from_bytes() {
        assert_eq!(super::from_bytes(0), 0);
        assert_eq!(super::from_bytes(1), 8);
        assert_eq!(super::from_bytes(2), 16);
    }

    #[test]
    fn to_bytes() {
        assert_eq!(super::to_bytes(0), 0);
        assert_eq!(super::to_bytes(1), 1);
        assert_eq!(super::to_bytes(8), 1);
        assert_eq!(super::to_bytes(9), 2);
        assert_eq!(super::to_bytes(16), 2);
        assert_eq!(super::to_bytes(17), 3);
    }
}
