use crate::modular::{mul::square_montgomery_form, Square};

use super::DynResidue;

impl<const LIMBS: usize> Square for DynResidue<LIMBS> {
    fn square(self) -> Self {
        DynResidue {
            montgomery_form: square_montgomery_form(
                &self.montgomery_form,
                self.residue_params.modulus,
                self.residue_params.mod_neg_inv,
            ),
            residue_params: self.residue_params,
        }
    }
}
