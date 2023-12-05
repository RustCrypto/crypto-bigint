//! Multiplicative inverses of boxed residue.

use super::BoxedResidue;
use crate::{modular::reduction::montgomery_reduction_boxed_mut, traits::Invert};
use subtle::CtOption;

impl BoxedResidue {
    /// Computes the residue `self^-1` representing the multiplicative inverse of `self`.
    /// I.e. `self * self^-1 = 1`.
    pub fn invert(&self) -> CtOption<Self> {
        let (mut inverse, is_some) = self
            .montgomery_form
            .inv_odd_mod(&self.residue_params.modulus);

        let mut product = inverse.mul(&self.residue_params.r3);

        montgomery_reduction_boxed_mut(
            &mut product,
            &self.residue_params.modulus,
            self.residue_params.mod_neg_inv,
            &mut inverse,
        );

        let value = Self {
            montgomery_form: inverse,
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
