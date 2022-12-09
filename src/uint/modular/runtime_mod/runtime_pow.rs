use crate::{
    modular::{pow::pow_montgomery_form, PowResidue},
    Uint,
};

use super::DynResidue;

impl<const LIMBS: usize> PowResidue<LIMBS> for DynResidue<LIMBS> {
    fn pow_specific(self, exponent: &Uint<LIMBS>, exponent_bits: usize) -> Self {
        self.pow_specific(exponent, exponent_bits)
    }
}

impl<const LIMBS: usize> DynResidue<LIMBS> {
    /// Computes the (reduced) exponentiation of a residue, here `exponent_bits` represents the number of bits to take into account for the exponent. Note that this value is leaked in the time pattern.
    pub const fn pow_specific(self, exponent: &Uint<LIMBS>, exponent_bits: usize) -> Self {
        Self {
            montgomery_form: pow_montgomery_form(
                self.montgomery_form,
                exponent,
                exponent_bits,
                self.residue_params.modulus,
                self.residue_params.r,
                self.residue_params.mod_neg_inv,
            ),
            residue_params: self.residue_params,
        }
    }
}
