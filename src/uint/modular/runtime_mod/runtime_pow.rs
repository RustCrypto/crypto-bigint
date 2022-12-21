use crate::{modular::pow::pow_montgomery_form, traits::Pow, Uint, Word};

use super::DynResidue;

impl<const LIMBS: usize> DynResidue<LIMBS> {
    /// Raises to the `exponent` power.
    pub const fn pow(&self, exponent: &Uint<LIMBS>) -> DynResidue<LIMBS> {
        self.pow_specific(exponent, LIMBS * Word::BITS as usize)
    }

    /// Raises to the `exponent` power,
    /// with `exponent_bits` representing the number of (least significant) bits
    /// to take into account for the exponent.
    ///
    /// NOTE: `exponent_bits` may be leaked in the time pattern.
    pub const fn pow_specific(&self, exponent: &Uint<LIMBS>, exponent_bits: usize) -> Self {
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

impl<const LIMBS: usize> Pow<Uint<LIMBS>> for DynResidue<LIMBS> {
    fn pow(&self, exponent: &Uint<LIMBS>) -> Self {
        self.pow(exponent)
    }

    fn pow_specific(&self, exponent: &Uint<LIMBS>, exponent_bits: usize) -> Self {
        self.pow_specific(exponent, exponent_bits)
    }
}
