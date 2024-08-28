//! Negations of boxed integers in Montgomery form.

use super::BoxedMontyForm;
use core::ops::Neg;

impl BoxedMontyForm {
    /// Negates the number.
    pub fn neg(&self) -> Self {
        Self {
            montgomery_form: self.montgomery_form.neg_mod(&self.params.modulus),
            params: self.params.clone(),
        }
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
