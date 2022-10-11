use core::ops::Neg;

use subtle::{Choice, ConditionallySelectable};

use crate::{UInt, Wrapping};

impl<const LIMBS: usize> Neg for Wrapping<UInt<LIMBS>> {
    type Output = Self;

    fn neg(self) -> Self::Output {
        let shifted = Wrapping(self.0.shl_vartime(1));
        self - shifted
    }
}

impl<const LIMBS: usize> UInt<LIMBS> {
    /// Negates based on `choice` by wrapping the integer.
    pub fn conditional_wrapping_neg(self, choice: Choice) -> UInt<LIMBS> {
        UInt::conditional_select(&self, &(-Wrapping(self)).0, choice)
    }
}
