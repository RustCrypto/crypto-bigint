use crate::{Limb, UInt, Word};

impl<const LIMBS: usize> UInt<LIMBS> {
    /// Calculate the number of bits needed to represent this number.
    #[allow(trivial_numeric_casts)]
    pub const fn bits(self) -> usize {
        let mut i = LIMBS - 1;
        while i > 0 && self.limbs[i].0 == 0 {
            i -= 1;
        }

        let limb = self.limbs[i].0;
        let bits = (Limb::BIT_SIZE * (i + 1)) as Word - limb.leading_zeros() as Word;

        Limb::ct_select(
            Limb(bits),
            Limb::ZERO,
            !self.limbs[0].is_nonzero() & !Limb(i as Word).is_nonzero(),
        )
        .0 as usize
    }
}
