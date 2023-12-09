//! Bit manipulation functions.

use crate::{BoxedUint, Limb, Zero};
use subtle::{Choice, ConditionallySelectable, ConstantTimeEq};

impl BoxedUint {
    /// Calculate the number of bits needed to represent this number, i.e. the index of the highest
    /// set bit.
    ///
    /// Use [`BoxedUint::bits_precision`] to get the total capacity of this integer.
    pub fn bits(&self) -> u32 {
        // Use `u32` because `subtle` can't select on `usize` and it matches what `core` uses for
        // the return value of `leading_zeros`
        let mut leading_zeros = 0u32;
        let mut n = 0u32;

        for limb in self.limbs.iter().rev() {
            n.conditional_assign(&(n + 1), !limb.is_zero() | !n.ct_eq(&0));

            // Set `leading_zeros` for the first nonzero limb we encounter
            leading_zeros.conditional_assign(&limb.leading_zeros(), n.ct_eq(&1));
        }

        Limb::BITS * n - leading_zeros
    }

    /// Calculate the number of bits needed to represent this number in variable-time with respect
    /// to `self`.
    pub fn bits_vartime(&self) -> u32 {
        let mut i = self.nlimbs() - 1;
        while i > 0 && self.limbs[i].0 == 0 {
            i -= 1;
        }

        let limb = self.limbs[i];
        Limb::BITS * (i as u32 + 1) - limb.leading_zeros()
    }

    /// Get the precision of this [`BoxedUint`] in bits.
    pub fn bits_precision(&self) -> u32 {
        self.limbs.len() as u32 * Limb::BITS
    }

    /// Calculate the number of trailing zeros in the binary representation of this number.
    pub fn trailing_zeros(&self) -> u32 {
        let mut count = 0;
        let mut nonzero_limb_not_encountered = Choice::from(1u8);

        for l in &*self.limbs {
            let z = l.trailing_zeros();
            count += u32::conditional_select(&0, &z, nonzero_limb_not_encountered);
            nonzero_limb_not_encountered &= l.is_zero();
        }

        count
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
}
