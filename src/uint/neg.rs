use core::ops::Neg;

use crate::{UInt, Word, Wrapping};

impl<const LIMBS: usize> Neg for Wrapping<UInt<LIMBS>> {
    type Output = Self;

    fn neg(self) -> Self::Output {
        let shifted = Wrapping(self.0.shl_vartime(1));
        self - shifted
    }
}

impl<const LIMBS: usize> UInt<LIMBS> {
    /// Negates based on `choice` by wrapping the integer.
    pub(crate) const fn conditional_wrapping_neg(self, choice: Word) -> UInt<LIMBS> {
        let (shifted, _) = self.shl_1();
        let negated_self = self.wrapping_sub(&shifted);

        UInt::ct_select(self, negated_self, choice)
    }
}
