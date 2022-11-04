use crate::{
    modular::pow::{pow_montgomery_form, PowResidue},
    UInt,
};

use super::Residue;

impl<const LIMBS: usize> PowResidue<LIMBS> for Residue<LIMBS> {
    fn pow_specific(self, exponent: &UInt<LIMBS>, exponent_bits: usize) -> Self {
        self.pow_specific(exponent, exponent_bits)
    }
}

impl<const LIMBS: usize> Residue<LIMBS> {
    pub const fn pow_specific(self, exponent: &UInt<LIMBS>, exponent_bits: usize) -> Self {
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
