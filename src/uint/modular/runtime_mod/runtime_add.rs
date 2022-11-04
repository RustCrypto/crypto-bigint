use core::ops::{Add, AddAssign};

use crate::modular::add::{add_montgomery_form, AddResidue};

use super::Residue;

impl<const LIMBS: usize> AddResidue for Residue<LIMBS> {
    fn add(&self, rhs: &Self) -> Self {
        debug_assert_eq!(self.residue_params, rhs.residue_params);
        Self {
            montgomery_form: add_montgomery_form(
                &self.montgomery_form,
                &rhs.montgomery_form,
                &self.residue_params.modulus,
            ),
            residue_params: self.residue_params,
        }
    }
}

impl<const LIMBS: usize> AddAssign for Residue<LIMBS> {
    fn add_assign(&mut self, rhs: Self) {
        self.montgomery_form = add_montgomery_form(
            &self.montgomery_form,
            &rhs.montgomery_form,
            &self.residue_params.modulus,
        );
    }
}

impl<const LIMBS: usize> Add for Residue<LIMBS> {
    type Output = Residue<LIMBS>;

    fn add(mut self, rhs: Self) -> Self::Output {
        self += rhs;
        self
    }
}
