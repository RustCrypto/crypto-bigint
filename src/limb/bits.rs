use crate::{BitOps, Choice, Word};

use super::Limb;

impl Limb {
    /// Calculate the number of bits needed to represent this number.
    #[inline(always)]
    #[must_use]
    pub const fn bits(self) -> u32 {
        Limb::BITS - self.0.leading_zeros()
    }

    /// Calculate the number of leading zeros in the binary representation of this number.
    #[inline(always)]
    #[must_use]
    pub const fn leading_zeros(self) -> u32 {
        self.0.leading_zeros()
    }

    /// Calculate the number of trailing zeros in the binary representation of this number.
    #[inline(always)]
    #[must_use]
    pub const fn trailing_zeros(self) -> u32 {
        self.0.trailing_zeros()
    }

    /// Calculate the number of trailing ones the binary representation of this number.
    #[inline(always)]
    #[must_use]
    pub const fn trailing_ones(self) -> u32 {
        self.0.trailing_ones()
    }

    /// Clear bits at or above the given bit position.
    #[must_use]
    pub const fn restrict_bits(self, len: u32) -> Self {
        #[allow(trivial_numeric_casts)]
        self.bitand(Limb((1 as Word).overflowing_shl(len).0 - 1))
    }
}

impl BitOps for Limb {
    #[inline(always)]
    fn bit(&self, index: u32) -> Choice {
        self.shr(index).lsb_to_choice()
    }

    #[inline(always)]
    fn bit_vartime(&self, index: u32) -> bool {
        self.shr(index).0 & 1 == 1
    }

    #[inline(always)]
    fn bits_precision(&self) -> u32 {
        Limb::BITS
    }

    #[inline(always)]
    fn bits(&self) -> u32 {
        Limb::BITS - self.0.leading_zeros()
    }

    #[inline(always)]
    fn bytes_precision(&self) -> usize {
        Limb::BYTES
    }

    #[inline(always)]
    fn leading_zeros(&self) -> u32 {
        self.0.leading_zeros()
    }

    #[inline(always)]
    fn log2_bits(&self) -> u32 {
        Limb::LOG2_BITS
    }

    #[inline(always)]
    fn set_bit(&mut self, index: u32, bit_value: Choice) {
        let mask = Limb::ONE.shl(index);
        *self = Limb::select(self.bitand(mask.not()), self.bitor(mask), bit_value);
    }

    #[inline(always)]
    fn set_bit_vartime(&mut self, index: u32, bit_value: bool) {
        if bit_value {
            *self = self.bitor(Limb::ONE.shl(index));
        } else {
            *self = self.bitand(Limb::ONE.shl(index).not());
        }
    }

    #[inline(always)]
    fn trailing_ones(&self) -> u32 {
        self.0.trailing_ones()
    }

    #[inline(always)]
    fn trailing_zeros(&self) -> u32 {
        self.0.trailing_zeros()
    }
}
