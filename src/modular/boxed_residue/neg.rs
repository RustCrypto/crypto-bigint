//! Negations of boxed residues.

use super::BoxedResidue;
use crate::BoxedUint;
use core::ops::Neg;

impl BoxedResidue {
    /// Negates the number.
    pub fn neg(&self) -> Self {
        let zero = Self {
            montgomery_form: BoxedUint::zero_with_precision(self.residue_params.bits_precision()),
            residue_params: self.residue_params.clone(),
        };

        zero.sub(self)
    }
}

impl Neg for BoxedResidue {
    type Output = Self;
    fn neg(self) -> Self {
        BoxedResidue::neg(&self)
    }
}

impl Neg for &BoxedResidue {
    type Output = BoxedResidue;
    fn neg(self) -> BoxedResidue {
        BoxedResidue::neg(self)
    }
}
