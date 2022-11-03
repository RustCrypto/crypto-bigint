use core::{marker::PhantomData, ops::MulAssign};

use super::{montgomery_reduction, Residue, ResidueParams};

impl<MOD: ResidueParams<LIMBS>, const LIMBS: usize> Residue<MOD, LIMBS> {
    /// Computes the (reduced) product between two residues.
    pub const fn mul(&self, rhs: &Self) -> Self {
        let product = self.montgomery_form.mul_wide(&rhs.montgomery_form);
        let montgomery_form = montgomery_reduction::<MOD, LIMBS>(product);

        Self {
            montgomery_form,
            phantom: PhantomData,
        }
    }
}

impl<MOD: ResidueParams<LIMBS>, const LIMBS: usize> Residue<MOD, LIMBS> {
    /// Computes the (reduced) square of a residue.
    pub const fn square(&self) -> Self {
        let lo_hi = self.montgomery_form.square_wide();

        Self {
            montgomery_form: montgomery_reduction::<MOD, LIMBS>(lo_hi),
            phantom: PhantomData,
        }
    }
}

impl<MOD: ResidueParams<LIMBS>, const LIMBS: usize> MulAssign for Residue<MOD, LIMBS> {
    fn mul_assign(&mut self, rhs: Self) {
        *self = self.mul(&rhs)
    }
}
