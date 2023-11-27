//! Bit manipulation functions.

use crate::{BoxedUint, Limb, Zero};
use subtle::{ConditionallySelectable, ConstantTimeEq};

impl BoxedUint {
    /// Calculate the number of bits needed to represent this number, i.e. the index of the highest
    /// set bit.
    ///
    /// Use [`BoxedUint::bits_precision`] to get the total capacity of this integer.
    pub fn bits(&self) -> usize {
        // Use `u32` because `subtle` can't select on `usize` and it matches what `core` uses for
        // the return value of `leading_zeros`
        let mut leading_zeros = 0u32;
        let mut n = 0u32;

        for limb in self.limbs.iter().rev() {
            n.conditional_assign(&(n + 1), !limb.is_zero() | !n.ct_eq(&0));

            // Set `leading_zeros` for the first nonzero limb we encounter
            leading_zeros.conditional_assign(&(limb.leading_zeros() as u32), n.ct_eq(&1));
        }

        Limb::BITS * (n as usize) - (leading_zeros as usize)
    }

    /// Get the precision of this [`BoxedUint`] in bits.
    pub fn bits_precision(&self) -> usize {
        self.limbs.len() * Limb::BITS
    }
}

#[cfg(test)]
mod tests {
    use super::BoxedUint;
    use hex_literal::hex;

    #[test]
    fn bits() {
        assert_eq!(0, BoxedUint::zero().bits());
        assert_eq!(128, BoxedUint::max(128).bits());

        let n1 = BoxedUint::from_be_slice(&hex!("000000000029ffffffffffffffffffff"), 128).unwrap();
        assert_eq!(86, n1.bits());

        let n2 = BoxedUint::from_be_slice(&hex!("00000000004000000000000000000000"), 128).unwrap();
        assert_eq!(87, n2.bits());
    }
}
