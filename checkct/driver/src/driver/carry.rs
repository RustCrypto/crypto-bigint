//! Regression checks for carry issues.

use super::private_limb;
use checkct_macros::checkct;
use core::hint::black_box;
use crypto_bigint::{Limb, NonZero, U256, Uint};

fn private_uint<const LIMBS: usize>() -> Uint<LIMBS> {
    let mut limbs = [Limb::ZERO; LIMBS];
    for limb in &mut limbs {
        *limb = private_limb();
    }
    Uint::new(limbs)
}

/// Keep the incoming carry unrestricted: it is a Word, not just a bit.
#[checkct]
pub fn limb_carrying_add() {
    black_box(private_limb().carrying_add(private_limb(), private_limb()));
}

/// Exercise the overflowing_add chain used by square root's high-half correction.
#[checkct]
pub fn add_assign_limb() {
    let mut value = private_uint::<4>();
    let carry = value.as_mut_uint_ref().add_assign_limb(private_limb());
    black_box((value, carry));
}

// The end-to-end regressions vary one secret bit at a time. Keep input references opaque at the
// call boundary to prevent witness-specific codegen. Do not add barriers inside the arithmetic or
// between carry propagation steps.

/// Toggle carry(x[0] + x[8]) in the first Karatsuba half-sum.
#[checkct]
pub fn widening_mul_carry_bit() {
    let mut limbs = [Limb::ZERO; 16];
    limbs[0] = Limb::MAX;
    limbs[8] = Limb(private_limb().0 & 1);
    black_box(widening_mul(
        black_box(&Uint::new(limbs)),
        black_box(&Uint::<16>::ONE),
    ));
}

/// Toggle overflow in the high-half correction of a 16-limb square.
#[checkct]
pub fn widening_square_carry_bit() {
    // For B = 2^(8 * Limb::BITS), use low half B-1 and high half
    // B/2 - 2^Limb::BITS - 1 - bit. At bit=0, z2.1's low limb is MAX
    // and the correction adds one; at bit=1 that limb is MAX-1.
    let mut limbs = [Limb::MAX; 16];
    limbs[15] = Limb(Limb::MAX.0 >> 1);
    limbs[8] = Limb(Limb::MAX.0 - (private_limb().0 & 1));
    limbs[9] = Limb(Limb::MAX.0 - 1);
    black_box(widening_square(black_box(&Uint::new(limbs))));
}

/// x = 2^255 or 2^255+1, d = 2^255+1: only the first requires the add-back.
#[checkct]
pub fn div_rem_add_back() {
    let high_bit = U256::ONE.shl_vartime(255);
    let divisor = high_bit.bitor(&U256::ONE).to_nz().unwrap();
    let mut dividend = high_bit;
    dividend.as_mut_limbs()[0] = Limb(private_limb().0 & 1);
    black_box(div_rem(black_box(&dividend), black_box(&divisor)));
}

// Keep input construction and its optimization barriers outside the arithmetic being checked.
// Sixteen limbs reach Karatsuba on both 32- and 64-bit targets.
#[inline(never)]
fn widening_mul<const LIMBS: usize>(
    a: &Uint<LIMBS>,
    b: &Uint<LIMBS>,
) -> (Uint<LIMBS>, Uint<LIMBS>) {
    a.widening_mul(b)
}

#[inline(never)]
fn widening_square<const LIMBS: usize>(value: &Uint<LIMBS>) -> (Uint<LIMBS>, Uint<LIMBS>) {
    value.widening_square()
}

#[inline(never)]
fn div_rem(dividend: &U256, divisor: &NonZero<U256>) -> (U256, U256) {
    dividend.div_rem(divisor)
}
