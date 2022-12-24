use crate::{Limb, Uint, Word};

impl<const LIMBS: usize> Uint<LIMBS> {
    /// Get the value of the bit at position `index`, as a 0- or 1-valued Word.
    /// Returns 0 for indices out of range.
    #[inline(always)]
    pub const fn bit_vartime(self, index: usize) -> Word {
        if index >= Self::BITS {
            0
        } else {
            (self.limbs[index / Limb::BITS].0 >> (index % Limb::BITS)) & 1
        }
    }

    /// Calculate the number of bits needed to represent this number.
    #[allow(trivial_numeric_casts)]
    pub const fn bits_vartime(self) -> usize {
        let mut i = LIMBS - 1;
        while i > 0 && self.limbs[i].0 == 0 {
            i -= 1;
        }

        let limb = self.limbs[i].0;
        let bits = (Limb::BITS * (i + 1)) as Word - limb.leading_zeros() as Word;

        Limb::ct_select(
            Limb(bits),
            Limb::ZERO,
            !self.limbs[0].is_nonzero() & !Limb(i as Word).is_nonzero(),
        )
        .0 as usize
    }

    /// Calculate the number of leading zeros in the binary representation of this number.
    pub const fn leading_zeros(self) -> usize {
        let limbs = self.as_limbs();

        let mut count: Word = 0;
        let mut i = LIMBS;
        let mut mask = Word::MAX;
        while i > 0 {
            i -= 1;
            let l = limbs[i];
            let z = l.leading_zeros() as Word;
            count += z & mask;
            mask &= !l.is_nonzero();
        }

        count as usize
    }

    /// Calculate the number of trailing zeros in the binary representation of this number.
    pub const fn trailing_zeros(self) -> usize {
        let limbs = self.as_limbs();

        let mut count: Word = 0;
        let mut i = 0;
        let mut mask = Word::MAX;
        while i < LIMBS {
            let l = limbs[i];
            let z = l.trailing_zeros() as Word;
            count += z & mask;
            mask &= !l.is_nonzero();
            i += 1;
        }

        count as usize
    }

    /// Calculate the number of bits needed to represent this number.
    pub const fn bits(self) -> usize {
        Self::BITS - self.leading_zeros()
    }

    /// Get the value of the bit at position `index`, as a 0- or 1-valued Word.
    /// Returns 0 for indices out of range.
    pub const fn bit(self, index: usize) -> Word {
        let limb_num = Limb((index / Limb::BITS) as Word);
        let index_in_limb = index % Limb::BITS;
        let index_mask = 1 << index_in_limb;

        let limbs = self.as_words();

        let mut result: Word = 0;
        let mut i = 0;
        while i < LIMBS {
            let bit = limbs[i] & index_mask;
            let is_right_limb = Limb::ct_eq(limb_num, Limb(i as Word));
            result |= bit & is_right_limb;
            i += 1;
        }

        result >> index_in_limb
    }
}

#[cfg(test)]
mod tests {
    use crate::U256;

    fn uint_with_bits_at(positions: &[usize]) -> U256 {
        let mut result = U256::ZERO;
        for pos in positions {
            result |= U256::ONE << *pos;
        }
        result
    }

    #[test]
    fn bit_vartime() {
        let u = uint_with_bits_at(&[16, 48, 112, 127, 255]);
        assert_eq!(u.bit_vartime(0), 0);
        assert_eq!(u.bit_vartime(1), 0);
        assert_eq!(u.bit_vartime(16), 1);
        assert_eq!(u.bit_vartime(127), 1);
        assert_eq!(u.bit_vartime(255), 1);
        assert_eq!(u.bit_vartime(256), 0);
        assert_eq!(u.bit_vartime(260), 0);
    }

    #[test]
    fn bit() {
        let u = uint_with_bits_at(&[16, 48, 112, 127, 255]);
        assert_eq!(u.bit(0), 0);
        assert_eq!(u.bit(1), 0);
        assert_eq!(u.bit(16), 1);
        assert_eq!(u.bit(127), 1);
        assert_eq!(u.bit(255), 1);
        assert_eq!(u.bit(256), 0);
        assert_eq!(u.bit(260), 0);
    }

    #[test]
    fn leading_zeros() {
        let u = uint_with_bits_at(&[256 - 16, 256 - 79, 256 - 207]);
        assert_eq!(u.leading_zeros() as u32, 15);

        let u = uint_with_bits_at(&[256 - 79, 256 - 207]);
        assert_eq!(u.leading_zeros() as u32, 78);

        let u = uint_with_bits_at(&[256 - 207]);
        assert_eq!(u.leading_zeros() as u32, 206);

        let u = uint_with_bits_at(&[256 - 1, 256 - 75, 256 - 150]);
        assert_eq!(u.leading_zeros() as u32, 0);

        let u = U256::ZERO;
        assert_eq!(u.leading_zeros() as u32, 256);
    }

    #[test]
    fn trailing_zeros() {
        let u = uint_with_bits_at(&[16, 79, 150]);
        assert_eq!(u.trailing_zeros() as u32, 16);

        let u = uint_with_bits_at(&[79, 150]);
        assert_eq!(u.trailing_zeros() as u32, 79);

        let u = uint_with_bits_at(&[150, 207]);
        assert_eq!(u.trailing_zeros() as u32, 150);

        let u = uint_with_bits_at(&[0, 150, 207]);
        assert_eq!(u.trailing_zeros() as u32, 0);

        let u = U256::ZERO;
        assert_eq!(u.trailing_zeros() as u32, 256);
    }
}
