//! Bit manipulation functions.

use crate::{BoxedUint, ConstChoice, Limb, Zero};
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

    /// `floor(log2(self.bits_precision()))`.
    pub(crate) fn log2_bits(&self) -> u32 {
        u32::BITS - self.bits_precision().leading_zeros() - 1
    }

    /// Returns `true` if the bit at position `index` is set, `false` otherwise.
    ///
    /// # Remarks
    /// This operation is variable time with respect to `index` only.
    pub fn bit_vartime(&self, index: u32) -> bool {
        if index >= self.bits_precision() {
            false
        } else {
            (self.limbs[(index / Limb::BITS) as usize].0 >> (index % Limb::BITS)) & 1 == 1
        }
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

    /// Calculate the number of trailing ones in the binary representation of this number.
    pub fn trailing_ones(&self) -> u32 {
        let limbs = self.as_limbs();

        let mut count = 0;
        let mut i = 0;
        let mut nonmax_limb_not_encountered = ConstChoice::TRUE;
        while i < limbs.len() {
            let l = limbs[i];
            let z = l.trailing_ones();
            count += nonmax_limb_not_encountered.if_true_u32(z);
            nonmax_limb_not_encountered =
                nonmax_limb_not_encountered.and(ConstChoice::from_word_eq(l.0, Limb::MAX.0));
            i += 1;
        }

        count
    }

    /// Calculate the number of trailing ones in the binary representation of this number,
    /// variable time in `self`.
    pub fn trailing_ones_vartime(&self) -> u32 {
        let limbs = self.as_limbs();

        let mut count = 0;
        let mut i = 0;
        while i < limbs.len() {
            let l = limbs[i];
            let z = l.trailing_ones();
            count += z;
            if z != Limb::BITS {
                break;
            }
            i += 1;
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
            result |= BoxedUint::one_with_precision(256).shl_vartime(pos).0;
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
