use crate::rng::{PrivateRng, PublicRng};
use checkct_macros::checkct;
use core::hint::black_box;
use crypto_bigint::{
    Limb, NonZero, U64, U128, U256, U384, U512, const_monty_params,
    modular::{ConstMontyForm, FixedMontyForm, FixedMontyParams},
};

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

// Use the public, always-inlined Limb methods to exercise the private primitives.
// Leave every input bit unconstrained, including noncanonical incoming borrow masks.
fn private_limb() -> Limb {
    let mut bytes = [0u8; Limb::BYTES];
    PrivateRng::new().fill_bytes(&mut bytes);
    Limb::from_le_bytes(bytes)
}

/// Exercise the difference and outgoing mask with a secret incoming borrow.
#[checkct]
pub fn limb_borrowing_sub() {
    black_box(private_limb().borrowing_sub(private_limb(), private_limb()));
}

/// Exercise the borrow mask in a conditional add-back of a public modulus.
#[checkct]
pub fn limb_borrowing_sub_add_back() {
    let mut bytes = [0u8; Limb::BYTES];
    PublicRng::new().fill_bytes(&mut bytes);
    let modulus = Limb::from_le_bytes(bytes);
    black_box(limb_sub_add_back(
        private_limb(),
        private_limb(),
        private_limb(),
        modulus,
    ));
}

#[inline(never)]
fn limb_sub_add_back(lhs: Limb, rhs: Limb, borrow: Limb, modulus: Limb) -> Limb {
    let (difference, borrow) = lhs.borrowing_sub(rhs, borrow);
    // Consume the mask directly: another Choice conversion or black_box here could hide
    // a regression in the primitive's optimization barrier.
    difference.wrapping_add(Limb(modulus.0 & borrow.0))
}

/// Exercise native and software leading-zero counts, including a secret zero input.
#[checkct]
pub fn limb_leading_zeros() {
    black_box(private_limb().leading_zeros());
}

/// Exercise native and software trailing-zero counts without constraining the input to be odd.
#[checkct]
pub fn limb_trailing_zeros() {
    black_box(private_limb().trailing_zeros());
}

/// Exercise trailing-zero counting of a complemented secret input, including all ones.
#[checkct]
pub fn limb_trailing_ones() {
    black_box(private_limb().trailing_ones());
}

/// Exercise a secret incoming borrow and its propagation across multiple limbs.
#[checkct]
pub fn borrowing_sub_u128() {
    let mut private = PrivateRng::new();
    let mut bytes = [0u8; 16];
    private.fill_bytes(&mut bytes);
    let a = U128::from_be_slice(&bytes);
    private.fill_bytes(&mut bytes);
    let b = U128::from_be_slice(&bytes);
    private.fill_bytes(&mut bytes);
    let borrow = U128::from_be_slice(&bytes).as_limbs()[0];

    black_box(borrowing_sub(&a, &b, borrow));
}

#[inline(never)]
fn borrowing_sub(a: &U128, b: &U128, borrow: Limb) -> (U128, Limb) {
    a.borrowing_sub(b, borrow)
}

/// Exercise a borrow chain whose final borrow is discarded.
#[checkct]
pub fn wrapping_sub_u128() {
    let mut private = PrivateRng::new();
    let mut bytes = [0u8; 16];
    private.fill_bytes(&mut bytes);
    let a = U128::from_be_slice(&bytes);
    private.fill_bytes(&mut bytes);
    let b = U128::from_be_slice(&bytes);
    black_box(wrapping_sub(&a, &b));
}

#[inline(never)]
fn wrapping_sub(a: &U128, b: &U128) -> U128 {
    a.wrapping_sub(b)
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

/// Exercise Montgomery carry propagation while converting a P-384 scalar.
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

/// Exercise Montgomery multiplication with two independent secret operands.
#[checkct]
pub fn montgomery_mul_u128() {
    let mut private = PrivateRng::new();
    let mut bytes = [0u8; 16];
    private.fill_bytes(&mut bytes);
    let a = U128::from_be_slice(&bytes);
    private.fill_bytes(&mut bytes);
    let b = U128::from_be_slice(&bytes);
    black_box(montgomery_mul(&a, &b));
}

#[inline(never)]
fn montgomery_mul(a: &U128, b: &U128) -> FixedMontyForm<{ U128::LIMBS }> {
    const PARAMS: FixedMontyParams<{ U128::LIMBS }> = FixedMontyParams::new_vartime(
        U128::from_be_hex("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFC5")
            .to_odd()
            .expect_copied("modulus is odd"),
    );
    FixedMontyForm::new(a, &PARAMS).mul(&FixedMontyForm::new(b, &PARAMS))
}

/// Exercise the shared multiplier with identical secret operands. U384 avoids
/// the four-limb wide-squaring shortcut on both 32-bit and 64-bit targets.
#[checkct]
pub fn montgomery_square_p384() {
    let mut bytes = [0u8; 48];
    PrivateRng::new().fill_bytes(&mut bytes);
    black_box(montgomery_square(&U384::from_be_slice(&bytes)));
}

#[inline(never)]
fn montgomery_square(value: &U384) -> ConstMontyForm<P384Order, { U384::LIMBS }> {
    ConstMontyForm::new(value).square()
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

/// Exercise the AMM exponentiation algorithm also used by `BoxedMontyForm::pow`.
/// The base and exponent are secret; the modulus and exponent bound are public.
#[checkct]
pub fn pow_amm_u128() {
    let mut private = PrivateRng::new();
    let mut bytes = [0u8; 16];
    private.fill_bytes(&mut bytes);
    let base = U128::from_be_slice(&bytes);
    private.fill_bytes(&mut bytes);
    let exponent = U128::from_be_slice(&bytes);
    black_box(pow_amm(&base, &exponent));
}

#[inline(never)]
fn pow_amm(base: &U128, exponent: &U128) -> U128 {
    const PARAMS: FixedMontyParams<{ U128::LIMBS }> = FixedMontyParams::new_vartime(
        U128::from_be_hex("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFC5")
            .to_odd()
            .expect_copied("modulus is odd"),
    );

    // U128 is multi-limb on every target. A fixed 65-bit bound crosses an exponent
    // limb boundary on both 32- and 64-bit targets and exercises a partial first
    // window followed by full windows, including when the exponent is zero.
    FixedMontyForm::new(base, &PARAMS)
        .pow_amm_bounded_exp(exponent, 65)
        .retrieve()
}
