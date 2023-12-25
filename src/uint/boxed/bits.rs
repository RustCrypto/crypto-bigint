//! Bit manipulation functions.

use crate::{
    uint::bits::{
        bit, bit_vartime, bits_vartime, leading_zeros, trailing_ones, trailing_ones_vartime,
        trailing_zeros, trailing_zeros_vartime,
    },
    BitOps, BoxedUint, Limb, Word,
};
use subtle::{Choice, ConditionallySelectable, ConstantTimeEq};

impl BoxedUint {
    /// Get the value of the bit at position `index`, as a truthy or falsy `Choice`.
    /// Returns the falsy value for indices out of range.
    pub fn bit(&self, index: u32) -> Choice {
        bit(&self.limbs, index).into()
    }

    /// Returns `true` if the bit at position `index` is set, `false` otherwise.
    ///
    /// # Remarks
    /// This operation is variable time with respect to `index` only.
    #[inline(always)]
    pub const fn bit_vartime(&self, index: u32) -> bool {
        bit_vartime(&self.limbs, index)
    }

    /// Calculate the number of bits needed to represent this number, i.e. the index of the highest
    /// set bit.
    ///
    /// Use [`BoxedUint::bits_precision`] to get the total capacity of this integer.
    pub fn bits(&self) -> u32 {
        self.bits_precision() - self.leading_zeros()
    }

    /// Calculate the number of bits needed to represent this number in variable-time with respect
    /// to `self`.
    pub fn bits_vartime(&self) -> u32 {
        bits_vartime(&self.limbs)
    }

    /// Calculate the number of leading zeros in the binary representation of this number.
    pub const fn leading_zeros(&self) -> u32 {
        leading_zeros(&self.limbs)
    }

    /// Get the precision of this [`BoxedUint`] in bits.
    pub fn bits_precision(&self) -> u32 {
        self.limbs.len() as u32 * Limb::BITS
    }

    /// Calculate the number of trailing zeros in the binary representation of this number.
    pub fn trailing_zeros(&self) -> u32 {
        trailing_zeros(&self.limbs)
    }

    /// Calculate the number of trailing ones in the binary representation of this number.
    pub fn trailing_ones(&self) -> u32 {
        trailing_ones(&self.limbs)
    }

    /// Calculate the number of trailing zeros in the binary representation of this number in
    /// variable-time with respect to `self`.
    pub fn trailing_zeros_vartime(&self) -> u32 {
        trailing_zeros_vartime(&self.limbs)
    }

    /// Calculate the number of trailing ones in the binary representation of this number,
    /// variable time in `self`.
    pub fn trailing_ones_vartime(&self) -> u32 {
        trailing_ones_vartime(&self.limbs)
    }

    /// Sets the bit at `index` to 0 or 1 depending on the value of `bit_value`.
    pub(crate) fn set_bit(&mut self, index: u32, bit_value: Choice) {
        let limb_num = (index / Limb::BITS) as usize;
        let index_in_limb = index % Limb::BITS;
        let index_mask = 1 << index_in_limb;

        for i in 0..self.nlimbs() {
            let limb = &mut self.limbs[i];
            let is_right_limb = i.ct_eq(&limb_num);
            let old_limb = *limb;
            let new_limb = Limb::conditional_select(
                &Limb(old_limb.0 & !index_mask),
                &Limb(old_limb.0 | index_mask),
                bit_value,
            );
            *limb = Limb::conditional_select(&old_limb, &new_limb, is_right_limb);
        }
    }

    pub(crate) fn set_bit_vartime(&mut self, index: u32, bit_value: bool) {
        let limb_num = (index / Limb::BITS) as usize;
        let index_in_limb = index % Limb::BITS;
        if bit_value {
            self.limbs[limb_num].0 |= 1 << index_in_limb;
        } else {
            #[allow(trivial_numeric_casts)]
            {
                self.limbs[limb_num].0 &= !((1 as Word) << index_in_limb);
            }
        }
    }
}

impl BitOps for BoxedUint {
    fn bits_precision(&self) -> u32 {
        self.bits_precision()
    }

    fn bytes_precision(&self) -> usize {
        self.nlimbs() * Limb::BYTES
    }

    fn leading_zeros(&self) -> u32 {
        self.leading_zeros()
    }

    fn bits(&self) -> u32 {
        self.bits()
    }

    fn bit(&self, index: u32) -> Choice {
        self.bit(index)
    }

    fn set_bit(&mut self, index: u32, bit_value: Choice) {
        self.set_bit(index, bit_value)
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
        self.set_bit_vartime(index, bit_value)
    }

    fn trailing_zeros_vartime(&self) -> u32 {
        self.trailing_zeros_vartime()
    }

    fn trailing_ones_vartime(&self) -> u32 {
        self.trailing_ones_vartime()
    }
}

#[cfg(test)]
mod tests {
    use super::BoxedUint;
    use hex_literal::hex;
    use subtle::Choice;

    fn uint_with_bits_at(positions: &[u32]) -> BoxedUint {
        let mut result = BoxedUint::zero_with_precision(256);
        for &pos in positions {
            result |= BoxedUint::one_with_precision(256).shl_vartime(pos).unwrap();
        }
        result
    }

    #[test]
    fn bit_vartime() {
        let u = uint_with_bits_at(&[16, 48, 112, 127, 255]);
        assert!(!u.bit_vartime(0));
        assert!(!u.bit_vartime(1));
        assert!(u.bit_vartime(16));
        assert!(u.bit_vartime(127));
        assert!(u.bit_vartime(255));
        assert!(!u.bit_vartime(256));
        assert!(!u.bit_vartime(260));
    }

    #[test]
    fn bits() {
        assert_eq!(0, BoxedUint::zero().bits());
        assert_eq!(128, BoxedUint::max(128).bits());

        let n1 = BoxedUint::from_be_slice(&hex!("000000000029ffffffffffffffffffff"), 128).unwrap();
        assert_eq!(86, n1.bits());

        let n2 = BoxedUint::from_be_slice(&hex!("00000000004000000000000000000000"), 128).unwrap();
        assert_eq!(87, n2.bits());
    }

    #[test]
    fn set_bit() {
        let mut u = uint_with_bits_at(&[16, 79, 150]);
        u.set_bit(127, Choice::from(1));
        assert_eq!(u, uint_with_bits_at(&[16, 79, 127, 150]));

        let mut u = uint_with_bits_at(&[16, 79, 150]);
        u.set_bit(150, Choice::from(1));
        assert_eq!(u, uint_with_bits_at(&[16, 79, 150]));

        let mut u = uint_with_bits_at(&[16, 79, 150]);
        u.set_bit(127, Choice::from(0));
        assert_eq!(u, uint_with_bits_at(&[16, 79, 150]));

        let mut u = uint_with_bits_at(&[16, 79, 150]);
        u.set_bit(150, Choice::from(0));
        assert_eq!(u, uint_with_bits_at(&[16, 79]));
    }

    #[test]
    fn trailing_ones() {
        let u = !uint_with_bits_at(&[16, 79, 150]);
        assert_eq!(u.trailing_ones(), 16);

        let u = !uint_with_bits_at(&[79, 150]);
        assert_eq!(u.trailing_ones(), 79);

        let u = !uint_with_bits_at(&[150, 207]);
        assert_eq!(u.trailing_ones(), 150);

        let u = !uint_with_bits_at(&[0, 150, 207]);
        assert_eq!(u.trailing_ones(), 0);

        let u = !BoxedUint::zero_with_precision(256);
        assert_eq!(u.trailing_ones(), 256);
    }

    #[test]
    fn trailing_ones_vartime() {
        let u = !uint_with_bits_at(&[16, 79, 150]);
        assert_eq!(u.trailing_ones_vartime(), 16);

        let u = !uint_with_bits_at(&[79, 150]);
        assert_eq!(u.trailing_ones_vartime(), 79);

        let u = !uint_with_bits_at(&[150, 207]);
        assert_eq!(u.trailing_ones_vartime(), 150);

        let u = !uint_with_bits_at(&[0, 150, 207]);
        assert_eq!(u.trailing_ones_vartime(), 0);

        let u = !BoxedUint::zero_with_precision(256);
        assert_eq!(u.trailing_ones_vartime(), 256);
    }
}
