use crate::{modular::reduction::montgomery_reduction, Limb, UInt, Word};

pub trait InvResidue {
    /// Computes the (reduced) multiplicative inverse of the residue.
    fn inv(self) -> Self;
}

pub const fn inv_montgomery_form<const LIMBS: usize>(
    x: UInt<LIMBS>,
    modulus: UInt<LIMBS>,
    r3: &UInt<LIMBS>,
    mod_neg_inv: Limb,
) -> UInt<LIMBS> {
    let (inverse, error) = x.inv_odd_mod(modulus);
    debug_assert!(error == Word::MAX);
    montgomery_reduction(inverse.mul_wide(r3), modulus, mod_neg_inv)
}
