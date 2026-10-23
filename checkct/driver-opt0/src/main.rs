#![no_std]
#![no_main]

use checkct_macros::checkct;
use core::hint::black_box;
use crypto_bigint::nlimbs;

#[path = "../../driver/src/rng.rs"]
mod rng;

use rng::{PrivateRng, PublicRng};

#[unsafe(no_mangle)]
pub extern "C" fn _start() -> ! {
    black_box(PublicRng::new().next_u32());
    panic!()
}

#[panic_handler]
fn panic(_info: &core::panic::PanicInfo) -> ! {
    __checkct_panic()
}

/// The analysis of a path stops when it reaches this function.
#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C" fn __checkct_panic() -> ! {
    loop {}
}

/// Exercise the branchless replacement for secret bit-length rounding.
#[checkct]
pub fn bits_to_limbs() {
    let bits = 127 + (PrivateRng::new().next_u32() & 1);
    black_box(nlimbs(bits));
}
