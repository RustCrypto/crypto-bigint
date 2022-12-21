use core::ops::{Mul, MulAssign};

use crate::{
    modular::mul::{mul_montgomery_form, square_montgomery_form},
    traits::Square,
};

use super::DynResidue;

impl<const LIMBS: usize> Mul<&DynResidue<LIMBS>> for &DynResidue<LIMBS> {
    type Output = DynResidue<LIMBS>;
    fn mul(self, rhs: &DynResidue<LIMBS>) -> DynResidue<LIMBS> {
        debug_assert_eq!(self.residue_params, rhs.residue_params);
        DynResidue {
            montgomery_form: mul_montgomery_form(
                &self.montgomery_form,
                &rhs.montgomery_form,
                self.residue_params.modulus,
                self.residue_params.mod_neg_inv,
            ),
            residue_params: self.residue_params,
        }
    }
}

impl<const LIMBS: usize> MulAssign<&DynResidue<LIMBS>> for DynResidue<LIMBS> {
    fn mul_assign(&mut self, rhs: &DynResidue<LIMBS>) {
        *self = self.mul(rhs);
    }
}

impl<const LIMBS: usize> Square for DynResidue<LIMBS> {
    fn square(&self) -> Self {
        Self {
            montgomery_form: square_montgomery_form(
                &self.montgomery_form,
                self.residue_params.modulus,
                self.residue_params.mod_neg_inv,
            ),
            residue_params: self.residue_params,
        }
    }
}
