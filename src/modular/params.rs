//! Helper functions for computing Montgomery parameters.
//!
//! These need to be `pub` as they're used by the `const_monty_params!` macro.

use crate::{Limb, Odd, Uint, Word};

/// Compute `1` in Montgomery form.
pub const fn montgomery_one<const LIMBS: usize>(modulus: &Odd<Uint<LIMBS>>) -> Uint<LIMBS> {
    Uint::MAX
        .rem_vartime(modulus.as_nz_ref())
        .wrapping_add(&Uint::ONE)
}

/// Compute `R^2` mod `modulus` in Montgomery form. Used to convert integers to Montgomery form.
pub const fn montgomery_r2<const LIMBS: usize>(
    one: &Uint<LIMBS>,
    modulus: &Odd<Uint<LIMBS>>,
) -> Uint<LIMBS> {
    Uint::rem_wide_vartime(one.square_wide(), modulus.as_nz_ref())
}

/// Compute the lowest limb of `-(modulus^-1) mod R`.
pub const fn mod_neg_inv<const LIMBS: usize>(modulus: &Odd<Uint<LIMBS>>) -> Limb {
    // The modular inverse should always exist, because it was ensured odd above, which also ensures
    // it's non-zero
    let inv_mod = modulus
        .as_ref()
        .invert_mod2k_vartime(Word::BITS)
        .expect("modular inverse should exist");

    Limb(Word::MIN.wrapping_sub(inv_mod.limbs[0].0))
}

/// Compute leading zeros in the modulus.
pub const fn mod_leading_zeros<const LIMBS: usize>(modulus: &Odd<Uint<LIMBS>>) -> u32 {
    let z = modulus.as_ref().leading_zeros();
    if z >= Word::BITS { Word::BITS - 1 } else { z }
}
