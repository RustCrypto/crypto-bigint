//! [`BoxedUint`] bitwise left shift operations.

use crate::{BoxedUint, Limb, Word};

impl BoxedUint {
    /// Computes `self << shift` where `0 <= shift < Limb::BITS`,
    /// returning the result and the carry.
    #[inline(always)]
    pub(crate) fn shl_limb(&self, n: usize) -> (Self, Limb) {
        let nlimbs = self.nlimbs();
        let mut limbs = vec![Limb::ZERO; nlimbs].into_boxed_slice();

        let nz = Limb(n as Word).ct_is_nonzero();
        let lshift = n as Word;
        let rshift = Limb::ct_select(Limb::ZERO, Limb((Limb::BITS - n) as Word), nz).0;
        let carry = Limb::ct_select(
            Limb::ZERO,
            Limb(self.limbs[nlimbs - 1].0.wrapping_shr(Word::BITS - n as u32)),
            nz,
        );

        let mut i = nlimbs - 1;
        while i > 0 {
            let mut limb = self.limbs[i].0 << lshift;
            let hi = self.limbs[i - 1].0 >> rshift;
            limb |= nz.if_true(hi);
            limbs[i] = Limb(limb);
            i -= 1
        }
        limbs[0] = Limb(self.limbs[0].0 << lshift);

        (Self { limbs }, carry)
    }

    /// Computes `self << shift`.
    ///
    /// NOTE: this operation is variable time with respect to `n` *ONLY*.
    ///
    /// When used with a fixed `n`, this function is constant-time with respect
    /// to `self`.
    #[inline(always)]
    pub fn shl_vartime(&self, n: usize) -> Self {
        let nlimbs = self.nlimbs();
        let mut limbs = vec![Limb::ZERO; nlimbs].into_boxed_slice();

        if n >= Limb::BITS * nlimbs {
            return Self { limbs };
        }

        let shift_num = n / Limb::BITS;
        let rem = n % Limb::BITS;

        let mut i = nlimbs;
        while i > shift_num {
            i -= 1;
            limbs[i] = self.limbs[i - shift_num];
        }

        let (new_lower, _carry) = (Self { limbs }).shl_limb(rem);
        new_lower
    }
}

#[cfg(test)]
mod tests {
    use super::BoxedUint;

    #[test]
    fn shl_vartime() {
        let one = BoxedUint::one_with_precision(128);

        assert_eq!(BoxedUint::from(2u8), one.shl_vartime(1));
        assert_eq!(BoxedUint::from(4u8), one.shl_vartime(2));
        assert_eq!(
            BoxedUint::from(0x80000000000000000u128),
            one.shl_vartime(67)
        );
    }
}
