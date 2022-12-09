use crate::{Limb, Uint, Word};

use super::mul::{mul_montgomery_form, square_montgomery_form};

/// Performs modular exponentiation using Montgomery's ladder. `exponent_bits` represents the number of bits to take into account for the exponent. Note that this value is leaked in the time pattern.
pub const fn pow_montgomery_form<const LIMBS: usize>(
    x: Uint<LIMBS>,
    exponent: &Uint<LIMBS>,
    exponent_bits: usize,
    modulus: Uint<LIMBS>,
    r: Uint<LIMBS>,
    mod_neg_inv: Limb,
) -> Uint<LIMBS> {
    let mut x1: Uint<LIMBS> = r;
    let mut x2: Uint<LIMBS> = x;

    // Shift the exponent all the way to the left so the leftmost bit is the MSB of the `Uint`
    let mut n: Uint<LIMBS> = exponent.shl_vartime((LIMBS * Word::BITS as usize) - exponent_bits);

    let mut i = 0;
    while i < exponent_bits {
        // Peel off one bit at a time from the left side
        let (next_n, overflow) = n.shl_1();
        n = next_n;

        let mut product: Uint<LIMBS> = x1;
        product = mul_montgomery_form(&product, &x2, modulus, mod_neg_inv);

        let mut square = Uint::ct_select(x1, x2, overflow);
        square = square_montgomery_form(&square, modulus, mod_neg_inv);

        x1 = Uint::<LIMBS>::ct_select(square, product, overflow);
        x2 = Uint::<LIMBS>::ct_select(product, square, overflow);

        i += 1;
    }

    x1
}
