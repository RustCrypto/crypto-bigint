//! Multiplicative inverses of boxed residue.

use super::BoxedResidue;
use crate::{modular::reduction::montgomery_reduction_boxed, traits::Invert};
use subtle::CtOption;

impl BoxedResidue {
    /// Computes the residue `self^-1` representing the multiplicative inverse of `self`.
    /// I.e. `self * self^-1 = 1`.
    pub fn invert(&self) -> CtOption<Self> {
        let (inverse, is_some) = self
            .montgomery_form
            .inv_odd_mod(&self.residue_params.modulus);

        let montgomery_form = montgomery_reduction_boxed(
            &mut inverse.mul(&self.residue_params.r3),
            &self.residue_params.modulus,
            self.residue_params.mod_neg_inv,
        );

        let value = Self {
            montgomery_form,
            residue_params: self.residue_params.clone(),
        };

        CtOption::new(value, is_some)
    }
}

impl Invert for BoxedResidue {
    type Output = CtOption<Self>;
    fn invert(&self) -> Self::Output {
        self.invert()
    }
}
