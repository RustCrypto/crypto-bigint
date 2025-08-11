use super::UintRef;
use crate::uint::bits::{
    bit, bit_vartime, bits_vartime, leading_zeros, set_bit, set_bit_vartime, trailing_ones,
    trailing_ones_vartime, trailing_zeros, trailing_zeros_vartime,
};
use crate::{Limb, traits::BitOps};
use subtle::Choice;

impl BitOps for UintRef {
    #[inline(always)]
    fn bits_precision(&self) -> u32 {
        self.0.len() as u32 * Limb::BITS
    }

    #[inline(always)]
    fn bytes_precision(&self) -> usize {
        self.0.len()
    }

    fn leading_zeros(&self) -> u32 {
        leading_zeros(self.as_slice())
    }

    fn bit(&self, index: u32) -> Choice {
        bit(self.as_slice(), index).into()
    }

    fn set_bit(&mut self, index: u32, bit_value: Choice) {
        set_bit(self.as_mut_slice(), index, bit_value.into());
    }

    fn trailing_zeros(&self) -> u32 {
        trailing_zeros(self.as_slice())
    }

    fn trailing_ones(&self) -> u32 {
        trailing_ones(self.as_slice())
    }

    fn bit_vartime(&self, index: u32) -> bool {
        bit_vartime(self.as_slice(), index)
    }

    fn bits_vartime(&self) -> u32 {
        bits_vartime(self.as_slice())
    }

    fn set_bit_vartime(&mut self, index: u32, bit_value: bool) {
        set_bit_vartime(self.as_mut_slice(), index, bit_value);
    }

    fn trailing_zeros_vartime(&self) -> u32 {
        trailing_zeros_vartime(self.as_slice())
    }

    fn trailing_ones_vartime(&self) -> u32 {
        trailing_ones_vartime(self.as_slice())
    }
}
