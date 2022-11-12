use crate::{Limb, UInt};

use super::reduction::montgomery_reduction;

pub trait MulResidue
where
    Self: Sized,
{
    /// Computes the (reduced) product of two residues.
    fn mul(&self, rhs: &Self) -> Self;

    fn square(&self) -> Self {
        self.mul(self)
    }
}

pub(crate) const fn mul_montgomery_form<const LIMBS: usize>(
    a: &UInt<LIMBS>,
    b: &UInt<LIMBS>,
    modulus: UInt<LIMBS>,
    mod_neg_inv: Limb,
) -> UInt<LIMBS> {
    let product = a.mul_wide(b);
    montgomery_reduction::<LIMBS>(product, modulus, mod_neg_inv)
}

pub(crate) const fn square_montgomery_form<const LIMBS: usize>(
    a: &UInt<LIMBS>,
    modulus: UInt<LIMBS>,
    mod_neg_inv: Limb,
) -> UInt<LIMBS> {
    let product = a.square_wide();
    montgomery_reduction::<LIMBS>(product, modulus, mod_neg_inv)
}
