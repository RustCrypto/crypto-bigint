//! Negations of boxed residues.

use super::BoxedResidue;
use core::ops::Neg;

impl BoxedResidue {
    /// Negates the number.
    pub fn neg(&self) -> Self {
        Self::zero(self.residue_params.clone()).sub(self)
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
