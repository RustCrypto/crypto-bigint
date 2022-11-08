use subtle::CtOption;

use crate::{modular::reduction::montgomery_reduction, Limb, UInt, Word};

pub trait InvResidue
where
    Self: Sized,
{
    /// Computes the (reduced) multiplicative inverse of the residue. Returns CtOption, which is None if the residue was not invertible.
    fn inv(self) -> CtOption<Self>;
}

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
