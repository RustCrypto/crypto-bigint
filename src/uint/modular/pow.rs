use crate::{Limb, Uint, Word};

use super::mul::{mul_montgomery_form, square_montgomery_form};

const WINDOW: usize = 4;
const WINDOW_MASK: Word = (1 << WINDOW) - 1;

/// Performs modular exponentiation using Montgomery's ladder.
/// `exponent_bits` represents the number of bits to take into account for the exponent.
///
/// NOTE: this value is leaked in the time pattern.
pub const fn pow_montgomery_form<const LIMBS: usize, const RHS_LIMBS: usize>(
    x: &Uint<LIMBS>,
    exponent: &Uint<RHS_LIMBS>,
    exponent_bits: usize,
    modulus: &Uint<LIMBS>,
    r: &Uint<LIMBS>,
    mod_neg_inv: Limb,
) -> Uint<LIMBS> {
    if exponent_bits == 0 {
        return *r; // 1 in Montgomery form
    }

    // powers[i] contains x^i
    let mut powers = [*r; 1 << WINDOW];
    powers[1] = *x;
    let mut i = 2;
    while i < powers.len() {
        powers[i] = mul_montgomery_form(&powers[i - 1], x, modulus, mod_neg_inv);
        i += 1;
    }

    multi_exponentiate_montgomery_form_internal(
        &[(powers, *exponent)],
        exponent_bits,
        modulus,
        r,
        mod_neg_inv,
    )
}

/// Performs modular multi-exponentiation using Montgomery's ladder.
/// `exponent_bits` represents the number of bits to take into account for the exponent.
///
/// See: Straus, E. G. Problems and solutions: Addition chains of vectors. American Mathematical Monthly 71 (1964), 806–808.
///
/// NOTE: this value is leaked in the time pattern.
#[cfg(feature = "alloc")]
pub fn multi_exponentiate_montgomery_form<const LIMBS: usize, const RHS_LIMBS: usize>(
    bases_and_exponents: &[(Uint<LIMBS>, Uint<RHS_LIMBS>)],
    exponent_bits: usize,
    modulus: &Uint<LIMBS>,
    r: &Uint<LIMBS>,
    mod_neg_inv: Limb,
) -> Uint<LIMBS> {
    if exponent_bits == 0 {
        return *r; // 1 in Montgomery form
    }

    let powers_and_exponents: alloc::vec::Vec<([Uint<LIMBS>; 1 << WINDOW], Uint<RHS_LIMBS>)> =
        bases_and_exponents
            .iter()
            .map(|(base, exponent)| {
                // powers[i] contains x^i
                let mut powers = [*r; 1 << WINDOW];
                powers[1] = *base;
                let mut i = 2;
                while i < powers.len() {
                    powers[i] = mul_montgomery_form(&powers[i - 1], base, modulus, mod_neg_inv);
                    i += 1;
                }
                (powers, *exponent)
            })
            .collect();

    multi_exponentiate_montgomery_form_internal(
        powers_and_exponents.as_slice(),
        exponent_bits,
        modulus,
        r,
        mod_neg_inv,
    )
}

const fn multi_exponentiate_montgomery_form_internal<const LIMBS: usize, const RHS_LIMBS: usize>(
    powers_and_exponents: &[([Uint<LIMBS>; 1 << WINDOW], Uint<RHS_LIMBS>)],
    exponent_bits: usize,
    modulus: &Uint<LIMBS>,
    r: &Uint<LIMBS>,
    mod_neg_inv: Limb,
) -> Uint<LIMBS> {
    let starting_limb = (exponent_bits - 1) / Limb::BITS;
    let starting_bit_in_limb = (exponent_bits - 1) % Limb::BITS;
    let starting_window = starting_bit_in_limb / WINDOW;
    let starting_window_mask = (1 << (starting_bit_in_limb % WINDOW + 1)) - 1;

    let mut z = *r; // 1 in Montgomery form

    let mut limb_num = starting_limb + 1;
    while limb_num > 0 {
        limb_num -= 1;

        let mut window_num = if limb_num == starting_limb {
            starting_window + 1
        } else {
            Limb::BITS / WINDOW
        };
        while window_num > 0 {
            window_num -= 1;

            if limb_num != starting_limb || window_num != starting_window {
                let mut i = 0;
                while i < WINDOW {
                    i += 1;
                    z = square_montgomery_form(&z, modulus, mod_neg_inv);
                }
            }

            let mut i = 0;
            while i < powers_and_exponents.len() {
                let (powers, exponent) = powers_and_exponents[i];
                let w = exponent.as_limbs()[limb_num].0;
                let mut idx = (w >> (window_num * WINDOW)) & WINDOW_MASK;

                if limb_num == starting_limb && window_num == starting_window {
                    idx &= starting_window_mask;
                }

                // Constant-time lookup in the array of powers
                let mut power = powers[0];
                let mut j = 1;
                while j < 1 << WINDOW {
                    let choice = Limb::ct_eq(Limb(j as Word), Limb(idx));
                    power = Uint::<LIMBS>::ct_select(&power, &powers[j], choice);
                    j += 1;
                }

                z = mul_montgomery_form(&z, &power, modulus, mod_neg_inv);
                i += 1;
            }
        }
    }

    z
}
