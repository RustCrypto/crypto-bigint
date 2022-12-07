use core::{
    marker::PhantomData,
    ops::{Mul, MulAssign},
};

use crate::modular::mul::mul_montgomery_form;

use super::{Residue, ResidueParams};

impl<MOD: ResidueParams<LIMBS>, const LIMBS: usize> Mul for Residue<MOD, LIMBS> {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self {
        Residue::mul(&self, &rhs)
    }
}

impl<MOD: ResidueParams<LIMBS>, const LIMBS: usize> MulAssign<Self> for Residue<MOD, LIMBS> {
    fn mul_assign(&mut self, rhs: Self) {
        *self = self.mul(rhs)
    }
}

impl<MOD: ResidueParams<LIMBS>, const LIMBS: usize> Residue<MOD, LIMBS> {
    /// Computes the (reduced) product between two residues.
    pub const fn mul(&self, rhs: &Self) -> Self {
        Residue {
            montgomery_form: mul_montgomery_form(
                &self.montgomery_form,
                &rhs.montgomery_form,
                MOD::MODULUS,
                MOD::MOD_NEG_INV,
            ),
            phantom: PhantomData,
        }
    }
}
