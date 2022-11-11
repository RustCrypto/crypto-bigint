use core::ops::{Mul, MulAssign};

use crate::modular::mul::{mul_montgomery_form, square_montgomery_form, MulResidue};

use super::DynResidue;

impl<const LIMBS: usize> MulResidue for DynResidue<LIMBS> {
    fn mul(&self, rhs: &Self) -> Self {
        debug_assert_eq!(self.residue_params, rhs.residue_params);
        Self {
            montgomery_form: mul_montgomery_form(
                &self.montgomery_form,
                &rhs.montgomery_form,
                self.residue_params.modulus,
                self.residue_params.mod_neg_inv,
            ),
            residue_params: self.residue_params,
        }
    }

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

impl<const LIMBS: usize> MulAssign for DynResidue<LIMBS> {
    fn mul_assign(&mut self, rhs: Self) {
        debug_assert_eq!(self.residue_params, rhs.residue_params);
        self.montgomery_form = mul_montgomery_form(
            &self.montgomery_form,
            &rhs.montgomery_form,
            self.residue_params.modulus,
            self.residue_params.mod_neg_inv,
        );
    }
}

impl<const LIMBS: usize> Mul for DynResidue<LIMBS> {
    type Output = DynResidue<LIMBS>;

    fn mul(mut self, rhs: Self) -> Self::Output {
        self *= rhs;
        self
    }
}
