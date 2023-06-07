extern crate alloc;
use alloc::vec::Vec;

use crate::{Limb, Uint, Word};

use super::mul::{mul_montgomery_form, square_montgomery_form};

/// Performs modular multi-exponentiation using Montgomery's ladder.
/// `exponent_bits` represents the number of bits to take into account for the exponent.
///
/// See: Straus, E. G. Problems and solutions: Addition chains of vectors. American Mathematical Monthly 71 (1964), 806–808.
///
/// NOTE: this value is leaked in the time pattern.
pub fn multi_exponentiate<const LIMBS: usize>(
    bases_and_exponents: Vec<(Uint<LIMBS>, Uint<LIMBS>)>,
    exponent_bits: usize,
    modulus: &Uint<LIMBS>,
    r: &Uint<LIMBS>,
    mod_neg_inv: Limb,
) -> Uint<LIMBS> {
    if exponent_bits == 0 {
        return *r; // 1 in Montgomery form
    }

    const WINDOW: usize = 4;
    const WINDOW_MASK: Word = (1 << WINDOW) - 1;

    let powers_and_exponents: Vec<([Uint<LIMBS>; 1 << WINDOW], Uint<LIMBS>)> = bases_and_exponents
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

            // TODO: I don't need  || window_num != starting_window right?
            if limb_num != starting_limb || window_num != starting_window {
                let mut i = 0;
                while i < WINDOW {
                    i += 1;
                    z = square_montgomery_form(&z, modulus, mod_neg_inv);
                }
            }

            powers_and_exponents.iter().for_each(|(powers, exponent)| {
                let w = exponent.as_limbs()[limb_num].0;
                let mut idx = (w >> (window_num * WINDOW)) & WINDOW_MASK;

                if limb_num == starting_limb && window_num == starting_window {
                    idx &= starting_window_mask;
                }

                // Constant-time lookup in the array of powers
                let mut power = powers[0];
                let mut i = 1;
                while i < 1 << WINDOW {
                    let choice = Limb::ct_eq(Limb(i as Word), Limb(idx));
                    power = Uint::<LIMBS>::ct_select(&power, &powers[i], choice);
                    i += 1;
                }

                z = mul_montgomery_form(&z, &power, modulus, mod_neg_inv);
            });
        }
    }

    z
}

#[cfg(test)]
mod tests {
    use crate::modular::multiexp::multi_exponentiate;
    use crate::{const_residue, impl_modulus, modular::constant_mod::ResidueParams, U256};
    use alloc::vec;

    impl_modulus!(
        Modulus,
        U256,
        "9CC24C5DF431A864188AB905AC751B727C9447A8E99E6366E1AD78A21E8D882B"
    );

    #[test]
    fn test_multi_exp() {
        let base =
            U256::from_be_hex("3435D18AA8313EBBE4D20002922225B53F75DC4453BB3EEC0378646F79B524A4");
        let base_mod = const_residue!(base, Modulus);

        let exponent =
            U256::from_be_hex("77117F1273373C26C700D076B3F780074D03339F56DD0EFB60E7F58441FD3685");

        let base2 =
            U256::from_be_hex("0431D18A08313EBBE4D20002922225B53F75DC4453BB3EEC0378646F79B524A4");
        let base2_mod = const_residue!(base2, Modulus);

        let exponent2 =
            U256::from_be_hex("77117F1273373C26C700D076B3F780074D03339F56DD0EFB60E7F58441FD3685");

        let expected = base_mod.pow(&exponent);

        let res = multi_exponentiate(
            vec![(base, exponent)],
            U256::BITS,
            &Modulus::MODULUS,
            &Modulus::R,
            Modulus::MOD_NEG_INV,
        );

        let res = const_residue!(res, Modulus);

        assert_eq!(res, expected);

        let expected = base_mod.pow(&exponent) * base2_mod.pow(&exponent2);

        let res = multi_exponentiate(
            vec![(base, exponent), (base2, exponent2)],
            U256::BITS,
            &Modulus::MODULUS,
            &Modulus::R,
            Modulus::MOD_NEG_INV,
        );

        let res = const_residue!(res, Modulus);

        assert_eq!(res, expected);
    }
}
