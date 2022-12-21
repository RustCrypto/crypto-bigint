use subtle::{Choice, CtOption};

use crate::{modular::inv::inv_montgomery_form, traits::Inv};

use super::DynResidue;

impl<const LIMBS: usize> DynResidue<LIMBS> {
    /// Computes the residue `self^-1` representing the multiplicative inverse of `self`.
    /// I.e. `self * self^-1 = 1`.
    /// If the number was invertible, the second element of the tuple is `1`,
    /// otherwise it is `0` (in which case the first element's value is unspecified).
    pub const fn inv(&self) -> (Self, u8) {
        let (montgomery_form, is_some) = inv_montgomery_form(
            self.montgomery_form,
            self.residue_params.modulus,
            &self.residue_params.r3,
            self.residue_params.mod_neg_inv,
        );

        let value = Self {
            montgomery_form,
            residue_params: self.residue_params,
        };

        (value, (is_some & 1) as u8)
    }
}

impl<const LIMBS: usize> Inv for DynResidue<LIMBS> {
    fn inv(&self) -> CtOption<Self> {
        let (value, is_some) = self.inv();
        CtOption::new(value, Choice::from(is_some))
    }
}
