use crate::{modular::reduction::montgomery_reduction, Limb, Uint, Word};

pub const fn inv_montgomery_form<const LIMBS: usize>(
    x: Uint<LIMBS>,
    modulus: Uint<LIMBS>,
    r3: &Uint<LIMBS>,
    mod_neg_inv: Limb,
) -> (Uint<LIMBS>, Word) {
    let (inverse, error) = x.inv_odd_mod(modulus);
    (
        montgomery_reduction(inverse.mul_wide(r3), modulus, mod_neg_inv),
        error,
    )
}
