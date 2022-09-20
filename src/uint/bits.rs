use crate::{Limb, UInt, Word};

impl<const LIMBS: usize> UInt<LIMBS> {
    /// Get the value of the bit at position `index`, as a 0- or 1-valued Word.
    #[inline]
    pub const fn bit(self, index: usize) -> Word {
        assert!(index < LIMBS * Limb::BIT_SIZE);
        (self.limbs[index / Limb::BIT_SIZE].0 >> (index % Limb::BIT_SIZE)) & 1
    }

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

#[cfg(test)]
mod tests {
    use crate::U64;

    #[test]
    fn bit_get_ok() {
        let u = U64::from_be_hex("d201000000010000");
        assert_eq!(u.bit(0), 0);
        assert_eq!(u.bit(1), 0);
        assert_eq!(u.bit(16), 1);
    }
}
