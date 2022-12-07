use subtle::{Choice, CtOption};

use crate::{
    modular::{inv::inv_montgomery_form, Inv},
    Word,
};

use super::DynResidue;

impl<const LIMBS: usize> Inv for DynResidue<LIMBS> {
    fn inv(self) -> CtOption<Self> {
        let (montgomery_form, error) = inv_montgomery_form(
            self.montgomery_form,
            self.residue_params.modulus,
            &self.residue_params.r3,
            self.residue_params.mod_neg_inv,
        );

        let value = DynResidue {
            montgomery_form,
            residue_params: self.residue_params,
        };

        CtOption::new(value, Choice::from((error == Word::MAX) as u8))
    }
}
