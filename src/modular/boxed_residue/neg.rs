//! Negations of boxed residues.

use super::BoxedMontyForm;
use crate::BoxedUint;
use core::ops::Neg;

impl BoxedMontyForm {
    /// Negates the number.
    pub fn neg(&self) -> Self {
        let zero = Self {
            montgomery_form: BoxedUint::zero_with_precision(self.residue_params.bits_precision()),
            residue_params: self.residue_params.clone(),
        };

        zero.sub(self)
    }
}

impl Neg for BoxedMontyForm {
    type Output = Self;
    fn neg(self) -> Self {
        BoxedMontyForm::neg(&self)
    }
}

impl Neg for &BoxedMontyForm {
    type Output = BoxedMontyForm;
    fn neg(self) -> BoxedMontyForm {
        BoxedMontyForm::neg(self)
    }
}
