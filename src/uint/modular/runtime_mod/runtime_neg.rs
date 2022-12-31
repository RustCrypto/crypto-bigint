use core::ops::Neg;

use super::DynResidue;

impl<const LIMBS: usize> DynResidue<LIMBS> {
    /// Negates the number.
    pub const fn neg(&self) -> Self {
        Self::zero(self.residue_params).sub(self)
    }
}

impl<const LIMBS: usize> Neg for DynResidue<LIMBS> {
    type Output = Self;
    fn neg(self) -> Self {
        (&self).neg()
    }
}
