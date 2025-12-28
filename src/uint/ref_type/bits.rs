use super::UintRef;
use crate::{ConstChoice, Limb, traits::BitOps, word};

impl UintRef {
    /// Get the precision of this number in bits.
    pub const fn bits_precision(&self) -> u32 {
        self.0.len() as u32 * Limb::BITS
    }

    /// Get the value of the bit at position `index`, as a truthy or falsy [`ConstChoice`].
    /// Returns the falsy value for indices out of range.
    #[inline(always)]
    pub const fn bit(&self, index: u32) -> ConstChoice {
        let limb_num = index / Limb::BITS;
        let index_in_limb = index % Limb::BITS;
        let index_mask = 1 << index_in_limb;

        let mut result = 0;
        let mut i = 0;
        while i < self.0.len() {
            let bit = self.0[i].0 & index_mask;
            let is_right_limb = ConstChoice::from_u32_eq(i as u32, limb_num);
            result |= word::select(0, bit, is_right_limb);
            i += 1;
        }

        word::choice_from_lsb(result >> index_in_limb)
    }

    /// Returns `true` if the bit at position `index` is set, `false` for an unset bit
    /// or for indices out of range.
    ///
    /// # Remarks
    /// This operation is variable time with respect to `index` only.
    #[inline(always)]
    pub const fn bit_vartime(&self, index: u32) -> bool {
        let limb_num = (index / Limb::BITS) as usize;
        let index_in_limb = index % Limb::BITS;
        if limb_num >= self.0.len() {
            false
        } else {
            (self.0[limb_num].0 >> index_in_limb) & 1 == 1
        }
    }

    /// Calculate the number of bits needed to represent this number, i.e. the index of the highest
    /// set bit.
    ///
    /// Use [`UintRef::bits_precision`] to get the total capacity of this integer.
    #[inline(always)]
    pub const fn bits(&self) -> u32 {
        self.bits_precision() - self.leading_zeros()
    }

    /// Calculate the number of bits needed to represent this number in variable-time with respect
    /// to `self`.
    #[inline(always)]
    pub const fn bits_vartime(&self) -> u32 {
        let mut i = self.0.len() - 1;
        while i > 0 && self.0[i].0 == 0 {
            i -= 1;
        }

        let limb = self.0[i];
        Limb::BITS * (i as u32 + 1) - limb.leading_zeros()
    }

    /// Sets the bit at `index` to 0 or 1 depending on the value of `bit_value`.
    #[inline(always)]
    pub const fn set_bit(&mut self, index: u32, bit_value: ConstChoice) {
        let limb_num = index / Limb::BITS;
        let index_in_limb = index % Limb::BITS;
        let index_mask = 1 << index_in_limb;

        let mut i = 0;
        while i < self.0.len() {
            let is_right_limb = ConstChoice::from_u32_eq(i as u32, limb_num);
            let old_limb = self.0[i].0;
            let new_limb = word::select(old_limb & !index_mask, old_limb | index_mask, bit_value);
            self.0[i] = Limb(word::select(old_limb, new_limb, is_right_limb));
            i += 1;
        }
    }

    /// Sets the bit at `index` to 0 or 1 depending on the value of `bit_value`, in variable-time
    /// with respect to `index`.
    #[inline(always)]
    pub const fn set_bit_vartime(&mut self, index: u32, bit_value: bool) {
        let limb_num = (index / Limb::BITS) as usize;
        let index_in_limb = index % Limb::BITS;
        if bit_value {
            self.0[limb_num].0 |= 1 << index_in_limb;
        } else {
            self.0[limb_num].0 &= !(1 << index_in_limb);
        }
    }

    /// Calculate the number of leading zeros in the binary representation of this number.
    pub const fn leading_zeros(&self) -> u32 {
        let mut count = 0;
        let mut i = self.0.len();
        let mut nonzero_limb_not_encountered = ConstChoice::TRUE;
        while i > 0 {
            i -= 1;
            let l = self.0[i];
            let z = l.leading_zeros();
            count += nonzero_limb_not_encountered.select_u32(0, z);
            nonzero_limb_not_encountered =
                nonzero_limb_not_encountered.and(word::choice_from_nonzero(l.0).not());
        }

        count
    }

    /// Calculate the number of trailing zeros in the binary representation of this number.
    #[inline(always)]
    pub const fn trailing_zeros(&self) -> u32 {
        let mut count = 0;
        let mut i = 0;
        let mut nonzero_limb_not_encountered = ConstChoice::TRUE;
        while i < self.0.len() {
            let l = self.0[i];
            let z = l.trailing_zeros();
            count += nonzero_limb_not_encountered.select_u32(0, z);
            nonzero_limb_not_encountered =
                nonzero_limb_not_encountered.and(word::choice_from_nonzero(l.0).not());
            i += 1;
        }

        count
    }

    /// Calculate the number of trailing zeros in the binary representation of this number, in
    /// variable-time with respect to `self`.
    #[inline(always)]
    pub const fn trailing_zeros_vartime(&self) -> u32 {
        let mut count = 0;
        let mut i = 0;
        while i < self.0.len() {
            let l = self.0[i];
            let z = l.trailing_zeros();
            count += z;
            if z != Limb::BITS {
                break;
            }
            i += 1;
        }

        count
    }

    /// Calculate the number of trailing ones in the binary representation of this number.
    #[inline(always)]
    pub const fn trailing_ones(&self) -> u32 {
        let mut count = 0;
        let mut i = 0;
        let mut nonmax_limb_not_encountered = ConstChoice::TRUE;
        while i < self.0.len() {
            let l = self.0[i];
            let z = l.trailing_ones();
            count += nonmax_limb_not_encountered.select_u32(0, z);
            nonmax_limb_not_encountered =
                nonmax_limb_not_encountered.and(word::choice_from_eq(l.0, Limb::MAX.0));
            i += 1;
        }

        count
    }

    /// Calculate the number of trailing ones in the binary representation of this number, in
    /// variable-time with respect to `self`.
    #[inline(always)]
    pub const fn trailing_ones_vartime(&self) -> u32 {
        let mut count = 0;
        let mut i = 0;
        while i < self.0.len() {
            let l = self.0[i];
            let z = l.trailing_ones();
            count += z;
            if z != Limb::BITS {
                break;
            }
            i += 1;
        }

        count
    }

    /// Clear all bits at or above a given bit position.
    pub const fn restrict_bits(&mut self, len: u32) {
        let limb = len / Limb::BITS;
        let limb_mask = Limb((1 << (len % Limb::BITS)) - 1);
        let mut i = 0;
        let mut clear = ConstChoice::FALSE;
        while i < self.nlimbs() {
            let apply = ConstChoice::from_u32_eq(i as u32, limb);
            self.0[i] = self.0[i].bitand(Limb::select(
                Limb(word::choice_to_mask(clear.not())),
                limb_mask,
                apply,
            ));
            clear = clear.or(apply);
            i += 1;
        }
    }
}

impl BitOps for UintRef {
    #[inline(always)]
    fn bits_precision(&self) -> u32 {
        self.bits_precision()
    }

    #[inline(always)]
    fn bytes_precision(&self) -> usize {
        self.0.len()
    }

    fn leading_zeros(&self) -> u32 {
        self.leading_zeros()
    }

    fn bit(&self, index: u32) -> ConstChoice {
        self.bit(index)
    }

    fn set_bit(&mut self, index: u32, bit_value: ConstChoice) {
        self.set_bit(index, bit_value);
    }

    fn trailing_zeros(&self) -> u32 {
        self.trailing_zeros()
    }

    fn trailing_ones(&self) -> u32 {
        self.trailing_ones()
    }

    fn bit_vartime(&self, index: u32) -> bool {
        self.bit_vartime(index)
    }

    fn bits_vartime(&self) -> u32 {
        self.bits_vartime()
    }

    fn set_bit_vartime(&mut self, index: u32, bit_value: bool) {
        self.set_bit_vartime(index, bit_value);
    }

    fn trailing_zeros_vartime(&self) -> u32 {
        self.trailing_zeros_vartime()
    }

    fn trailing_ones_vartime(&self) -> u32 {
        self.trailing_ones_vartime()
    }
}
