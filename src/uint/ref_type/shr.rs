//! [`UintRef`] bitwise right shift operations.

use super::UintRef;
use crate::{Choice, Limb, NonZero, primitives::u32_bits};

#[cfg(feature = "alloc")]
use crate::primitives::u32_rem;

#[cfg(feature = "alloc")]
use crate::word;

impl UintRef {
    /// Right-shifts by `shift` bits.
    ///
    /// # Panics
    /// - if the shift exceeds the type's width.
    #[inline(always)]
    #[cfg(feature = "alloc")]
    pub(crate) const fn shr_assign(&mut self, shift: u32) {
        self.bounded_shr_assign(shift, self.bits_precision());
    }

    /// Right-shifts by `shift` bits in constant-time.
    ///
    /// Returns truthy `Choice` and leaves `self` unmodified if `shift >= self.bits_precision()`,
    /// otherwise returns a falsy `Choice` and shifts `self` in place.
    #[cfg(feature = "alloc")]
    #[inline(always)]
    pub const fn overflowing_shr_assign(&mut self, shift: u32) -> Choice {
        let bits = self.bits_precision();
        let overflow = Choice::from_u32_le(bits, shift);
        let shift = overflow.select_u32(shift, 0);
        self.bounded_shr_assign(shift, bits);
        overflow
    }

    /// Right-shifts by `shift` bits, producing zero if the shift exceeds the precision.
    #[cfg(feature = "alloc")]
    #[inline(always)]
    pub(crate) const fn unbounded_shr_assign(&mut self, shift: u32) {
        let overflow = self.overflowing_shr_assign(shift);
        self.conditional_set_zero(overflow);
    }

    /// Right-shifts by `shift` bits where `shift < shift_upper_bound`, producing zero if
    /// the shift exceeds the precision.
    ///
    /// The runtime is determined by `shift_upper_bound` which may be smaller than
    /// `self.bits_precision()`.
    ///
    /// # Panics
    /// - if the shift exceeds the upper bound.
    #[cfg(feature = "alloc")]
    #[inline(always)]
    pub(crate) const fn bounded_shr_assign(&mut self, shift: u32, shift_upper_bound: u32) {
        assert!(shift < shift_upper_bound, "`shift` exceeds upper bound");

        if shift_upper_bound <= Limb::BITS {
            self.shr_assign_limb(shift);
        } else {
            self.bounded_shr_by_limbs_assign(
                shift >> Limb::LOG2_BITS,
                shift_upper_bound.div_ceil(Limb::BITS),
            );
            self.shr_assign_limb(shift & (Limb::BITS - 1));
        }
    }

    /// Right-shifts by `shift * Limb::BITS` bits where `shift < shift_upper_bound`.
    ///
    /// The runtime is determined by `shift_upper_bound` which may be larger or smaller than
    /// `self.bits_precision()`.
    ///
    /// # Panics
    /// - if the shift exceeds the upper bound.
    #[inline(always)]
    pub(crate) const fn bounded_shr_by_limbs_assign(&mut self, shift: u32, shift_upper_bound: u32) {
        assert!(shift < shift_upper_bound, "`shift` exceeds upper bound");

        let shift_bits = u32_bits(shift_upper_bound - 1);
        let mut i = 0;
        while i < shift_bits {
            let bit = Choice::from_u32_lsb(shift >> i);
            self.conditional_shr_assign_by_limbs_vartime(1 << i, bit);
            i += 1;
        }
    }

    /// Conditionally right-shifts by `shift` limbs in a panic-free manner, producing zero
    /// if the shift exceeds the precision.
    ///
    /// NOTE: this operation is variable time with respect to `shift` *ONLY*.
    ///
    /// When used with a fixed `shift`, this function is constant-time with respect to `self`.
    #[inline(always)]
    pub(crate) const fn conditional_shr_assign_by_limbs_vartime(&mut self, shift: u32, c: Choice) {
        let shift = shift as usize;
        let mut i = 0;
        while i < self.nlimbs().saturating_sub(shift) {
            self.limbs[i] = Limb::select(self.limbs[i], self.limbs[i + shift], c);
            i += 1;
        }
        while i < self.nlimbs() {
            self.limbs[i] = Limb::select(self.limbs[i], Limb::ZERO, c);
            i += 1;
        }
    }

    /// Right-shifts by `shift` limbs in a panic-free manner, producing zero if the shift
    /// exceeds the precision.
    #[inline(always)]
    #[allow(clippy::cast_possible_truncation)]
    pub(crate) const fn unbounded_shr_assign_by_limbs(&mut self, shift: u32) {
        let nlimbs = self.nlimbs() as u32;
        let overflow = Choice::from_u32_le(nlimbs, shift);
        let shift = overflow.select_u32(shift, 0);
        self.bounded_shr_by_limbs_assign(shift, nlimbs);
        self.conditional_set_zero(overflow);
    }

    /// Right-shifts by `shift` limbs in a panic-free manner, producing zero if the shift
    /// exceeds the precision.
    ///
    /// NOTE: this operation is variable time with respect to `shift` *ONLY*.
    ///
    /// When used with a fixed `shift`, this function is constant-time with respect to `self`.
    #[inline(always)]
    pub(crate) const fn unbounded_shr_assign_by_limbs_vartime(&mut self, shift: u32) {
        let shift = shift as usize;
        let mut i = 0;
        while i < self.nlimbs().saturating_sub(shift) {
            self.limbs[i] = self.limbs[i + shift];
            i += 1;
        }
        while i < self.nlimbs() {
            self.limbs[i] = Limb::ZERO;
            i += 1;
        }
    }

    /// Right-shifts by `shift` bits in a panic-free manner, producing zero if the shift
    /// exceeds the precision.
    ///
    /// NOTE: this operation is variable time with respect to `shift` *ONLY*.
    ///
    /// When used with a fixed `shift`, this function is constant-time with respect to `self`.
    #[cfg(feature = "alloc")]
    #[inline(always)]
    pub const fn unbounded_shr_assign_vartime(&mut self, shift: u32) {
        let shift_limbs = shift / Limb::BITS;
        let rem = shift % Limb::BITS;

        self.unbounded_shr_assign_by_limbs_vartime(shift_limbs);

        if rem > 0 {
            let mut carry = Limb::ZERO;
            let mut i = self.nlimbs().saturating_sub(shift_limbs as usize);
            while i > 0 {
                i -= 1;
                (self.limbs[i], carry) = (
                    self.limbs[i].shr(rem).bitor(carry),
                    self.limbs[i].shl(Limb::BITS - rem),
                );
            }
        }
    }

    /// Right-shifts by `shift` bits in a panic-free manner, reducing shift modulo the type's width.
    #[inline(always)]
    #[cfg(feature = "alloc")]
    pub(crate) const fn wrapping_shr_assign(&mut self, shift: u32) {
        self.shr_assign(u32_rem(shift, self.bits_precision()));
    }

    /// Right-shifts by `shift` bits in a panic-free manner, reducing shift modulo the type's width.
    ///
    /// NOTE: this operation is variable time with respect to `shift` *ONLY*.
    ///
    /// When used with a fixed `shift`, this function is constant-time with respect to `self`.
    #[inline(always)]
    #[cfg(feature = "alloc")]
    pub(crate) const fn wrapping_shr_assign_vartime(&mut self, shift: u32) {
        self.unbounded_shr_assign_vartime(shift % self.bits_precision());
    }

    /// Right-shifts by a single bit in constant-time, returning [`Choice::TRUE`]
    /// if the least significant bit was set, and [`Choice::FALSE`] otherwise.
    #[cfg(feature = "alloc")]
    #[inline(always)]
    pub const fn shr1_assign(&mut self) -> Choice {
        let mut carry = Limb::ZERO;
        let mut i = self.nlimbs();
        while i > 0 {
            i -= 1;
            let (limb, new_carry) = self.limbs[i].shr1();
            self.limbs[i] = limb.bitor(carry);
            carry = new_carry;
        }
        word::choice_from_lsb(carry.0 >> Limb::HI_BIT)
    }

    /// Conditionally right-shifts by `shift` bits where `0 < shift < Limb::BITS`, returning
    /// the carry.
    ///
    /// # Panics
    /// - if `shift >= Limb::BITS`.
    #[inline(always)]
    pub(crate) const fn conditional_shr_assign_limb_nonzero(
        &mut self,
        shift: NonZero<u32>,
        choice: Choice,
    ) -> Limb {
        assert!(shift.0 < Limb::BITS);

        let rshift = shift.0;
        let lshift = Limb::BITS - shift.0;
        let mut carry = Limb::ZERO;

        let mut i = self.nlimbs();
        while i > 0 {
            i -= 1;
            (self.limbs[i], carry) = (
                Limb::select(
                    self.limbs[i],
                    self.limbs[i].shr(rshift).bitor(carry),
                    choice,
                ),
                self.limbs[i].shl(lshift),
            );
        }

        Limb::select(Limb::ZERO, carry, choice)
    }

    /// Right-shifts by `shift` bits where `0 < shift < Limb::BITS`, returning the carry.
    ///
    /// # Panics
    /// - if `shift >= Limb::BITS`.
    #[inline(always)]
    pub const fn shr_assign_limb(&mut self, shift: u32) -> Limb {
        let nz = Choice::from_u32_nz(shift);
        self.conditional_shr_assign_limb_nonzero(NonZero(nz.select_u32(1, shift)), nz)
    }

    /// Right-shifts by `shift` bits where `0 < shift < Limb::BITS`, returning
    /// the carry.
    ///
    /// NOTE: this operation is variable time with respect to `shift` *ONLY*.
    ///
    /// When used with a fixed `shift`, this function is constant-time with respect to `self`.
    ///
    /// # Panics
    /// If the shift size is equal to or larger than the width of the integer.
    #[inline(always)]
    pub const fn shr_assign_limb_vartime(&mut self, shift: u32) -> Limb {
        assert!(shift < Limb::BITS);

        if shift == 0 {
            return Limb::ZERO;
        }

        let rshift = shift;
        let lshift = Limb::BITS - shift;
        let mut carry = Limb::ZERO;

        let mut i = self.nlimbs();
        while i > 0 {
            i -= 1;
            (self.limbs[i], carry) = (
                self.limbs[i].shr(rshift).bitor(carry),
                self.limbs[i].shl(lshift),
            );
        }

        carry
    }
}

#[cfg(test)]
mod tests {
    use crate::Uint;
    #[cfg(feature = "alloc")]
    use crate::{Limb, U256};

    #[cfg(feature = "alloc")]
    const N: U256 =
        U256::from_be_hex("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141");

    #[cfg(feature = "alloc")]
    const N_2: U256 =
        U256::from_be_hex("7FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF5D576E7357A4501DDFE92F46681B20A0");

    #[cfg(feature = "alloc")]
    #[test]
    fn shr1_assign() {
        let mut n = N;
        let carry = n.as_mut_uint_ref().shr1_assign();
        assert_eq!(n, N_2);
        assert!(carry.to_bool());

        let mut m = U256::MAX;
        let carry = m.as_mut_uint_ref().shr1_assign();
        assert_eq!(m, U256::MAX.shr_vartime(1));
        assert!(carry.to_bool());

        let mut z = U256::ZERO;
        let carry = z.as_mut_uint_ref().shr1_assign();
        assert_eq!(z, U256::ZERO);
        assert!(!carry.to_bool());
    }

    #[cfg(feature = "alloc")]
    #[test]
    fn shr256() {
        let mut n = N;
        assert!(bool::from(n.as_mut_uint_ref().overflowing_shr_assign(256)));
    }

    #[cfg(feature = "alloc")]
    #[test]
    fn shr_assign_limb() {
        // Shift by zero
        let mut val = N;
        let carry = val.as_mut_uint_ref().shr_assign_limb(0);
        assert_eq!(val, N);
        assert_eq!(carry, Limb::ZERO);

        // Shift by one
        let mut val = N;
        let carry = val.as_mut_uint_ref().shr_assign_limb(1);
        assert_eq!(val, N.shr_vartime(1));
        assert_eq!(carry, N.limbs[0].shl(Limb::BITS - 1));

        // Shift by any
        let mut val = N;
        let carry = val.as_mut_uint_ref().shr_assign_limb(13);
        assert_eq!(val, N.shr_vartime(13));
        assert_eq!(carry, N.limbs[0].shl(Limb::BITS - 13));

        // Shift by max
        let mut val = N;
        let carry = val.as_mut_uint_ref().shr_assign_limb(Limb::BITS - 1);
        assert_eq!(val, N.shr_vartime(Limb::BITS - 1));
        assert_eq!(carry, N.limbs[0].shl(1));
    }

    #[test]
    fn unbounded_shr_by_limbs_vartime() {
        let refval = Uint::<2>::from_words([1, 99]);

        let mut val = refval;
        val.as_mut_uint_ref()
            .unbounded_shr_assign_by_limbs_vartime(0);
        assert_eq!(val.as_words(), &[1, 99]);

        let mut val = refval;
        val.as_mut_uint_ref()
            .unbounded_shr_assign_by_limbs_vartime(1);
        assert_eq!(val.as_words(), &[99, 0]);

        let mut val = refval;
        val.as_mut_uint_ref()
            .unbounded_shr_assign_by_limbs_vartime(2);
        assert_eq!(val.as_words(), &[0, 0]);
    }

    #[cfg(feature = "alloc")]
    #[test]
    fn compare_shr_assign() {
        for i in 0..256 {
            let (mut a, mut b) = (N, N);
            a.as_mut_uint_ref().bounded_shr_assign(i, 256);
            b.as_mut_uint_ref().unbounded_shr_assign_vartime(i);
            assert_eq!(a, b);
        }
    }
}
