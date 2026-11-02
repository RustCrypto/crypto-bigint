#![no_std]

use checkct_macros::checkct;
use core::hint::black_box;
use crypto_bigint::nlimbs;

#[path = "../../driver/src/rng.rs"]
mod rng;

use rng::{PrivateRng, PublicRng};

// Keep the harness in this crate so the package profile controls its opt-level.
#[inline(never)]
pub fn start() -> ! {
    black_box(PublicRng::new().next_u32());
    panic!()
}

/// Exercise the branchless replacement for secret bit-length rounding.
#[checkct]
pub fn bits_to_limbs() {
    let bits = 127 + (PrivateRng::new().next_u32() & 1);
    black_box(nlimbs(bits));
}
