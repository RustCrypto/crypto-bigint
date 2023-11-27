//! [`BoxedUint`] bitwise right shift operations.

use crate::{BoxedUint, Limb};

impl BoxedUint {
    /// Computes `self >> shift`.
    ///
    /// NOTE: this operation is variable time with respect to `shift` *ONLY*.
    ///
    /// When used with a fixed `shift`, this function is constant-time with respect to `self`.
    #[inline(always)]
    pub fn shr_vartime(&self, shift: usize) -> Self {
        let nlimbs = self.nlimbs();
        let full_shifts = shift / Limb::BITS;
        let small_shift = shift & (Limb::BITS - 1);
        let mut limbs = vec![Limb::ZERO; nlimbs].into_boxed_slice();

        if shift > Limb::BITS * nlimbs {
            return Self { limbs };
        }

        let n = nlimbs - full_shifts;
        let mut i = 0;

        if small_shift == 0 {
            while i < n {
                limbs[i] = Limb(self.limbs[i + full_shifts].0);
                i += 1;
            }
        } else {
            while i < n {
                let mut lo = self.limbs[i + full_shifts].0 >> small_shift;

                if i < (nlimbs - 1) - full_shifts {
                    lo |= self.limbs[i + full_shifts + 1].0 << (Limb::BITS - small_shift);
                }

                limbs[i] = Limb(lo);
                i += 1;
            }
        }

        Self { limbs }
    }
}

#[cfg(test)]
mod tests {
    use super::BoxedUint;

    #[test]
    fn shr_vartime() {
        let n = BoxedUint::from(0x80000000000000000u128);
        assert_eq!(BoxedUint::zero(), n.shr_vartime(68));
        assert_eq!(BoxedUint::one(), n.shr_vartime(67));
        assert_eq!(BoxedUint::from(2u8), n.shr_vartime(66));
        assert_eq!(BoxedUint::from(4u8), n.shr_vartime(65));
    }
}
