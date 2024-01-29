//! Negations of integers in Montgomery form with a modulus set at runtime.

use super::MontyForm;
use core::ops::Neg;

impl<const LIMBS: usize> MontyForm<LIMBS> {
    /// Negates the number.
    #[must_use]
    pub const fn neg(&self) -> Self {
        Self::zero(self.params).sub(self)
    }
}

impl<const LIMBS: usize> Neg for MontyForm<LIMBS> {
    type Output = Self;
    fn neg(self) -> Self {
        MontyForm::neg(&self)
    }
}

impl<const LIMBS: usize> Neg for &MontyForm<LIMBS> {
    type Output = MontyForm<LIMBS>;
    fn neg(self) -> MontyForm<LIMBS> {
        MontyForm::neg(self)
    }
}
