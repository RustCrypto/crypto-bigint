use crate::{
    modular::{pow::pow_montgomery_form, Pow},
    UInt,
};

use super::DynResidue;

impl<const LIMBS: usize> Pow<LIMBS> for DynResidue<LIMBS> {
    fn pow_specific(self, exponent: &UInt<LIMBS>, exponent_bits: usize) -> Self {
        DynResidue {
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
