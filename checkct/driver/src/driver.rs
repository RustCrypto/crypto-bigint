use crate::rng::{PrivateRng, PublicRng};
use checkct_macros::checkct;
use core::hint::black_box;
use crypto_bigint::{NonZero, U64, U256, U384, U512, const_monty_params, modular::ConstMontyForm};

const_monty_params!(
    P384Order,
    U384,
    "ffffffffffffffffffffffffffffffffffffffffffffffffc7634d81f4372ddf581a0db248b0a77aecec196accc52973"
);

// Generate inputs that previously triggered non-constant-time behavior.
fn inputs() -> (U256, U256, NonZero<U256>) {
    let mut private = PrivateRng::new();
    let mut public = PublicRng::new();
    let mut bytes = [0u8; 32];

    private.fill_bytes(&mut bytes);
    bytes[0] &= 0x7f;
    let a = U256::from_be_slice(&bytes);

    private.fill_bytes(&mut bytes);
    bytes[0] &= 0x7f;
    let b = U256::from_be_slice(&bytes);

    public.fill_bytes(&mut bytes);
    bytes[0] |= 0x80;
    let p = U256::from_be_slice(&bytes).to_nz().unwrap();

    (a, b, p)
}

#[checkct]
pub fn sub_mod_u256() {
    let (a, b, p) = inputs();
    black_box(a.sub_mod(&b, &p));
}

/// Exercise the shared limb scan used by `Uint` and `BoxedUint` modular inversion.
#[checkct]
pub fn trailing_zeros_u512() {
    let mut bytes = [0u8; 64];
    PrivateRng::new().fill_bytes(&mut bytes);
    bytes[63] |= 1;

    // An odd integer has no trailing zeros, but the scan still processes its higher secret limbs.
    // Keep that fact outside the counting function.
    black_box(trailing_zeros(&U512::from_be_slice(&bytes)));
}

#[inline(never)]
fn trailing_zeros(value: &U512) -> u32 {
    value.trailing_zeros()
}

/// Exercise the shared limb scan used to normalize a secret divisor.
#[checkct]
pub fn leading_zeros_u512() {
    let mut bytes = [0u8; 64];
    PrivateRng::new().fill_bytes(&mut bytes);
    black_box(leading_zeros(&U512::from_be_slice(&bytes)));
}

#[inline(never)]
fn leading_zeros(value: &U512) -> u32 {
    value.leading_zeros()
}

/// Exercise division with two independent secret operands and a nonzero divisor.
/// `U64` keeps symbolic execution small while remaining multi-limb on RISCV32 and Thumb-1.
#[checkct]
pub fn div_rem_u64() {
    let mut private = PrivateRng::new();
    let mut bytes = [0u8; 8];
    private.fill_bytes(&mut bytes);
    let dividend = U64::from_be_slice(&bytes);

    private.fill_bytes(&mut bytes);
    bytes[7] |= 1;
    let divisor = U64::from_be_slice(&bytes).to_nz().unwrap();

    black_box(div_rem(&dividend, &divisor));
}

#[inline(never)]
fn div_rem(dividend: &U64, divisor: &NonZero<U64>) -> (U64, U64) {
    dividend.div_rem(divisor)
}

/// Exercise wide overflowing addition while converting a P-384 scalar.
#[checkct]
pub fn montgomery_form_p384() {
    let mut bytes = [0u8; 48];
    PrivateRng::new().fill_bytes(&mut bytes);
    bytes[0] &= 0x7f; // Values below 2^383 are below the scalar modulus.
    black_box(to_montgomery_p384(&U384::from_be_slice(&bytes)));
}

#[inline(never)]
fn to_montgomery_p384(value: &U384) -> ConstMontyForm<P384Order, { U384::LIMBS }> {
    ConstMontyForm::new(value)
}

/// Exercise exact division with a secret divisor whose trailing zeros are not fixed.
#[checkct]
pub fn div_exact_u64() {
    let mut bytes = [0u8; 8];
    let mut private = PrivateRng::new();
    private.fill_bytes(&mut bytes);
    let dividend = U64::from_be_slice(&bytes);
    private.fill_bytes(&mut bytes);
    bytes[0] |= 1; // Keep the divisor nonzero while allowing an even divisor.
    let divisor = U64::from_be_slice(&bytes).to_nz().unwrap();
    black_box(div_exact(&dividend, &divisor));
}

#[inline(never)]
fn div_exact(dividend: &U64, divisor: &NonZero<U64>) -> crypto_bigint::CtOption<U64> {
    dividend.div_exact(divisor)
}

/// Exercise the separate double-width remainder path with secret operands.
#[checkct]
pub fn rem_wide_u64() {
    let mut bytes = [0u8; 8];
    let mut private = PrivateRng::new();
    private.fill_bytes(&mut bytes);
    let lower = U64::from_be_slice(&bytes);
    private.fill_bytes(&mut bytes);
    let upper = U64::from_be_slice(&bytes);
    private.fill_bytes(&mut bytes);
    bytes[7] |= 1;
    let divisor = U64::from_be_slice(&bytes).to_nz().unwrap();
    black_box(rem_wide((lower, upper), &divisor));
}

#[inline(never)]
fn rem_wide(value: (U64, U64), divisor: &NonZero<U64>) -> U64 {
    U64::rem_wide(value, divisor)
}
