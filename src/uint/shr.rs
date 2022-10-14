//! [`UInt`] bitwise right shift operations.

use super::UInt;
use crate::{limb::HI_BIT, Limb, Word};
use core::ops::{Shr, ShrAssign};

impl<const LIMBS: usize> UInt<LIMBS> {
    /// Computes `self >> 1` in constant-time, returning the overflowing bit as a `Word` that is either 0...0 or 1...1.
    pub(crate) const fn shr_1(&self) -> (Self, Word) {
        let mut shifted_bits = [0; LIMBS];
        let mut i = 0;
        while i < LIMBS {
            shifted_bits[i] = self.limbs[i].0 >> 1;
            i += 1;
        }

        let mut carry_bits = [0; LIMBS];
        let mut i = 0;
        while i < LIMBS {
            carry_bits[i] = self.limbs[i].0 << HI_BIT;
            i += 1;
        }

        let mut limbs = [Limb(0); LIMBS];

        let mut i = 0;
        while i < (LIMBS - 1) {
            limbs[i] = Limb(shifted_bits[i] | carry_bits[i + 1]);
            i += 1;
        }
        limbs[LIMBS - 1] = Limb(shifted_bits[LIMBS - 1]);

        (
            UInt::new(limbs),
            (carry_bits[0] >> HI_BIT).wrapping_mul(Word::MAX),
        )
    }

    /// Computes `self >> n`.
    ///
    /// NOTE: this operation is variable time with respect to `n` *ONLY*.
    ///
    /// When used with a fixed `n`, this function is constant-time with respect
    /// to `self`.
    #[inline(always)]
    pub const fn shr_vartime(&self, shift: usize) -> Self {
        let full_shifts = shift / Limb::BIT_SIZE;
        let small_shift = shift & (Limb::BIT_SIZE - 1);
        let mut limbs = [Limb::ZERO; LIMBS];

        if shift > Limb::BIT_SIZE * LIMBS {
            return Self { limbs };
        }

        let n = LIMBS - full_shifts;
        let mut i = 0;

        if small_shift == 0 {
            while i < n {
                limbs[i] = Limb(self.limbs[i + full_shifts].0);
                i += 1;
            }
        } else {
            while i < n {
                let mut lo = self.limbs[i + full_shifts].0 >> small_shift;

                if i < (LIMBS - 1) - full_shifts {
                    lo |= self.limbs[i + full_shifts + 1].0 << (Limb::BIT_SIZE - small_shift);
                }

                limbs[i] = Limb(lo);
                i += 1;
            }
        }

        Self { limbs }
    }

    /// Computes a right shift on a wide input as `(lo, hi)`.
    ///
    /// NOTE: this operation is variable time with respect to `n` *ONLY*.
    ///
    /// When used with a fixed `n`, this function is constant-time with respect
    /// to `self`.
    #[inline(always)]
    pub const fn shr_vartime_wide(lower_upper: (Self, Self), n: usize) -> (Self, Self) {
        let (mut lower, upper) = lower_upper;
        let new_upper = upper.shr_vartime(n);
        lower = lower.shr_vartime(n);
        if n >= LIMBS * Limb::BIT_SIZE {
            lower = lower.bitor(&upper.shr_vartime(n - LIMBS * Limb::BIT_SIZE));
        } else {
            lower = lower.bitor(&upper.shl_vartime(LIMBS * Limb::BIT_SIZE - n));
        }

        (lower, new_upper)
    }
}

impl<const LIMBS: usize> Shr<usize> for UInt<LIMBS> {
    type Output = UInt<LIMBS>;

    /// NOTE: this operation is variable time with respect to `rhs` *ONLY*.
    ///
    /// When used with a fixed `rhs`, this function is constant-time with respect
    /// to `self`.
    fn shr(self, rhs: usize) -> UInt<LIMBS> {
        self.shr_vartime(rhs)
    }
}

impl<const LIMBS: usize> Shr<usize> for &UInt<LIMBS> {
    type Output = UInt<LIMBS>;

    /// NOTE: this operation is variable time with respect to `rhs` *ONLY*.
    ///
    /// When used with a fixed `rhs`, this function is constant-time with respect
    /// to `self`.
    fn shr(self, rhs: usize) -> UInt<LIMBS> {
        self.shr_vartime(rhs)
    }
}

impl<const LIMBS: usize> ShrAssign<usize> for UInt<LIMBS> {
    fn shr_assign(&mut self, rhs: usize) {
        *self = self.shr_vartime(rhs);
    }
}

#[cfg(test)]
mod tests {
    use crate::{UInt, U128, U256};

    const N: U256 =
        U256::from_be_hex("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141");

    const N_2: U256 =
        U256::from_be_hex("7FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF5D576E7357A4501DDFE92F46681B20A0");

    #[test]
    fn shr1() {
        assert_eq!(N >> 1, N_2);
    }

    #[test]
    fn shr_wide_1_1_128() {
        assert_eq!(
            UInt::shr_vartime_wide((U128::ONE, U128::ONE), 128),
            (U128::ONE, U128::ZERO)
        );
    }

    #[test]
    fn shr_wide_0_max_1() {
        assert_eq!(
            UInt::shr_vartime_wide((U128::ZERO, U128::MAX), 1),
            (U128::ONE << 127, U128::MAX >> 1)
        );
    }

    #[test]
    fn shr_wide_max_max_256() {
        assert_eq!(
            UInt::shr_vartime_wide((U128::MAX, U128::MAX), 256),
            (U128::ZERO, U128::ZERO)
        );
    }
}
