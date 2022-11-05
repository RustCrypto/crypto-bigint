use crate::modular::inv::{inv_montgomery_form, InvResidue};

use super::Residue;

impl<const LIMBS: usize> InvResidue for Residue<LIMBS> {
    fn inv(self) -> Self {
        Self {
            montgomery_form: inv_montgomery_form(
                self.montgomery_form,
                self.residue_params.modulus,
                &self.residue_params.r3,
                self.residue_params.mod_neg_inv,
            ),
            residue_params: self.residue_params,
        }
    }
}
