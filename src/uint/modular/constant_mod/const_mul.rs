use core::{
    marker::PhantomData,
    ops::{Mul, MulAssign},
};

use crate::modular::{
    mul::{mul_montgomery_form, MulResidue},
    reduction::montgomery_reduction,
};

use super::{Residue, ResidueParams};

impl<MOD: ResidueParams<LIMBS>, const LIMBS: usize> MulResidue for Residue<MOD, LIMBS> {
    fn mul(&self, rhs: &Self) -> Self {
        self.mul(rhs)
    }

    fn square(&self) -> Self {
        self.square()
    }
}

impl<MOD: ResidueParams<LIMBS>, const LIMBS: usize> Residue<MOD, LIMBS> {
    /// Computes the (reduced) product between two residues.
    pub const fn mul(&self, rhs: &Self) -> Self {
        Self {
            montgomery_form: mul_montgomery_form(
                &self.montgomery_form,
                &rhs.montgomery_form,
                MOD::MODULUS,
                MOD::MOD_NEG_INV,
            ),
            phantom: PhantomData,
        }
    }

    /// Computes the (reduced) square of a residue.
    pub const fn square(&self) -> Self {
        let lo_hi = self.montgomery_form.square_wide();

        Self {
            montgomery_form: montgomery_reduction::<LIMBS>(lo_hi, MOD::MODULUS, MOD::MOD_NEG_INV),
            phantom: PhantomData,
        }
    }
}

impl<MOD: ResidueParams<LIMBS>, const LIMBS: usize> MulAssign<&Self> for Residue<MOD, LIMBS> {
    fn mul_assign(&mut self, rhs: &Self) {
        *self = self.mul(rhs)
    }
}

impl<MOD: ResidueParams<LIMBS>, const LIMBS: usize> Mul for &Residue<MOD, LIMBS> {
    type Output = Residue<MOD, LIMBS>;

    fn mul(self, rhs: Self) -> Self::Output {
        self.mul(rhs)
    }
}
