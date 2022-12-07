use core::marker::PhantomData;

use crate::modular::{reduction::montgomery_reduction, Square};

use super::{Residue, ResidueParams};

impl<MOD: ResidueParams<LIMBS>, const LIMBS: usize> Square for Residue<MOD, LIMBS> {
    fn square(self) -> Self {
        Residue::square(&self)
    }
}

impl<MOD: ResidueParams<LIMBS>, const LIMBS: usize> Residue<MOD, LIMBS> {
    /// Computes the (reduced) square of a residue.
    pub const fn square(&self) -> Self {
        let lo_hi = self.montgomery_form.square_wide();

        Self {
            montgomery_form: montgomery_reduction::<LIMBS>(lo_hi, MOD::MODULUS, MOD::MOD_NEG_INV),
            phantom: PhantomData,
        }
    }
}
