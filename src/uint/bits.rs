use crate::limb::{Inner, BIT_SIZE};
use crate::{Limb, UInt};

impl<const LIMBS: usize> UInt<LIMBS> {
    /// Calculate the number of bits needed to represent this number
    pub(crate) const fn bits(self) -> Inner {
        let mut i = LIMBS - 1;
        while i > 0 && self.limbs[i].0 == 0 {
            i -= 1;
        }

        let limb = self.limbs[i].0;
        let bits = (BIT_SIZE * (i + 1)) as Inner - limb.leading_zeros() as Inner;

        Limb::ct_select(
            Limb(bits),
            Limb::ZERO,
            !self.limbs[0].is_nonzero() & !Limb(i as Inner).is_nonzero(),
        )
        .0
    }
}
