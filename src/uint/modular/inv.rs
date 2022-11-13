use crate::{modular::reduction::montgomery_reduction, Limb, UInt, Word};

pub const fn inv_montgomery_form<const LIMBS: usize>(
    x: UInt<LIMBS>,
    modulus: UInt<LIMBS>,
    r3: &UInt<LIMBS>,
    mod_neg_inv: Limb,
) -> (UInt<LIMBS>, Word) {
    let (inverse, error) = x.inv_odd_mod(modulus);
    (
        montgomery_reduction(inverse.mul_wide(r3), modulus, mod_neg_inv),
        error,
    )
}
