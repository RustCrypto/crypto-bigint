//! [`BoxedUint`] bitwise left shift operations.

use crate::{BoxedUint, Choice, Limb, Shl, ShlAssign, ShlVartime, WrappingShl};

impl BoxedUint {
    /// Computes `self << shift`.
    ///
    /// # Panics
    /// - if `shift >= Self::BITS`.
    #[must_use]
    pub fn shl(&self, shift: u32) -> BoxedUint {
        let (result, overflow) = self.overflowing_shl(shift);
        assert!(!bool::from(overflow), "attempt to shift left with overflow");
        result
    }

    /// Computes `self <<= shift`.
    ///
    /// # Panics
    /// - if `shift >= Self::BITS`.
    pub fn shl_assign(&mut self, shift: u32) {
        let overflow = self.overflowing_shl_assign(shift);
        assert!(!bool::from(overflow), "attempt to shift left with overflow");
    }

    /// Computes `self << shift`.
    ///
    /// Returns `self` and a truthy `Choice` if `shift >= self.bits_precision()`,
    /// or the result and a falsy `Choice` otherwise.
    #[must_use]
    pub fn overflowing_shl(&self, shift: u32) -> (Self, Choice) {
        let mut result = self.clone();
        let overflow = result.as_mut_uint_ref().overflowing_shl_assign(shift);
        (result, overflow)
    }

    /// Computes `self << shift` in variable-time.
    ///
    /// Returns `None` if `shift >= self.bits_precision()`, otherwise the shifted result.
    #[must_use]
    pub fn overflowing_shl_vartime(&self, shift: u32) -> Option<Self> {
        if shift < self.bits_precision() {
            let mut result = self.clone();
            result.as_mut_uint_ref().wrapping_shl_assign_vartime(shift);
            Some(result)
        } else {
            None
        }
    }

    /// Computes `self <<= shift`.
    ///
    /// Returns a truthy `Choice` if `shift >= self.bits_precision()` or a falsy `Choice` otherwise.
    pub fn overflowing_shl_assign(&mut self, shift: u32) -> Choice {
        self.as_mut_uint_ref().overflowing_shl_assign(shift)
    }

    /// Computes `self <<= shift` in variable-time.
    ///
    /// If `shift >= self.bits_precision()`, shifts `self` in place and returns `false`.
    /// Otherwise returns `true` and leaves `self` unmodified.
    pub fn overflowing_shl_assign_vartime(&mut self, shift: u32) -> bool {
        if shift < self.bits_precision() {
            self.as_mut_uint_ref().wrapping_shl_assign_vartime(shift);
            false
        } else {
            true
        }
    }

    /// Computes `self << shift` in a panic-free manner, masking off bits of `shift` which would cause the shift to
    /// exceed the type's width.
    #[must_use]
    pub fn wrapping_shl(&self, shift: u32) -> Self {
        let mut result = self.clone();
        result.wrapping_shl_assign(shift);
        result
    }

    /// Computes `self <<= shift` in a panic-free manner, masking off bits of `shift` which would cause the shift to
    /// exceed the type's width.
    pub fn wrapping_shl_assign(&mut self, shift: u32) {
        // self is zeroed in the case of an overflowing shift
        self.as_mut_uint_ref().wrapping_shl_assign(shift);
    }

    /// Computes `self << shift` in variable-time in a panic-free manner, masking off bits of `shift` which would cause
    /// the shift to exceed the type's width.
    #[must_use]
    pub fn wrapping_shl_vartime(&self, shift: u32) -> Self {
        let mut result = self.clone();
        result.as_mut_uint_ref().wrapping_shl_assign_vartime(shift);
        result
    }

    /// Computes `self <<= shift` in variable-time in a panic-free manner, producing zero in the case of overflow.
    pub fn wrapping_shl_assign_vartime(&mut self, shift: u32) {
        self.as_mut_uint_ref().wrapping_shl_assign_vartime(shift);
    }

    /// Computes `self << shift`.
    /// Returns `None` if `shift >= self.bits_precision()`.
    ///
    /// NOTE: this operation is variable time with respect to `shift` *ONLY*.
    ///
    /// When used with a fixed `shift`, this function is constant-time with respect to `self`.
    #[inline(always)]
    #[must_use]
    pub fn shl_vartime(&self, shift: u32) -> Option<Self> {
        // This could use `UintRef::wrapping_shl_assign_vartime`, but it is faster to operate
        // on a zero'ed clone and let the compiler reuse the memory allocation when possible.

        let nbits = self.bits_precision();
        if shift >= nbits {
            return None;
        }

        let mut dest = Self::zero_with_precision(nbits);
        let nlimbs = self.nlimbs();
        let shift_limbs = (shift / Limb::BITS) as usize;
        let rem = shift % Limb::BITS;

        for i in shift_limbs..nlimbs {
            dest.limbs[i] = self.limbs[i - shift_limbs];
        }

        if rem > 0 {
            dest.as_mut_uint_ref_range(shift_limbs..nlimbs)
                .shl_assign_limb(rem);
        }

        Some(dest)
    }

    /// Computes `self << 1` in constant-time.
    pub(crate) fn shl1(&self) -> (Self, Limb) {
        let mut ret = self.clone();
        let carry = Limb::select(Limb::ZERO, Limb::ONE, ret.shl1_assign());
        (ret, carry)
    }

    /// Computes `self <<= 1` in constant-time.
    pub(crate) fn shl1_assign(&mut self) -> Choice {
        self.as_mut_uint_ref().shl1_assign()
    }
}

macro_rules! impl_shl {
    ($($shift:ty),+) => {
        $(
            impl Shl<$shift> for BoxedUint {
                type Output = BoxedUint;

                #[inline]
                fn shl(self, shift: $shift) -> BoxedUint {
                    <&Self>::shl(&self, shift)
                }
            }

            impl Shl<$shift> for &BoxedUint {
                type Output = BoxedUint;

                #[inline]
                fn shl(self, shift: $shift) -> BoxedUint {
                    BoxedUint::shl(self, u32::try_from(shift).expect("invalid shift"))
                }
            }

            impl ShlAssign<$shift> for BoxedUint {
                fn shl_assign(&mut self, shift: $shift) {
                    BoxedUint::shl_assign(self, u32::try_from(shift).expect("invalid shift"))
                }
            }
        )+
    };
}

impl_shl!(i32, u32, usize);

impl WrappingShl for BoxedUint {
    fn wrapping_shl(&self, shift: u32) -> BoxedUint {
        self.wrapping_shl(shift)
    }
}

impl ShlVartime for BoxedUint {
    fn overflowing_shl_vartime(&self, shift: u32) -> Option<Self> {
        self.overflowing_shl_vartime(shift)
    }

    fn wrapping_shl_vartime(&self, shift: u32) -> Self {
        self.wrapping_shl_vartime(shift)
    }
}

#[cfg(test)]
mod tests {
    use super::BoxedUint;

    #[test]
    fn shl() {
        let one = BoxedUint::one_with_precision(128);

        assert_eq!(BoxedUint::from(2u8), &one << 1);
        assert_eq!(BoxedUint::from(4u8), &one << 2);
        assert_eq!(
            BoxedUint::from(0x80000000000000000u128),
            one.shl_vartime(67).unwrap()
        );
    }

    #[test]
    fn shl1_assign() {
        let mut n = BoxedUint::from(0x3c442b21f19185fe433f0a65af902b8fu128);
        let n_shl1 = BoxedUint::from(0x78885643e3230bfc867e14cb5f20571eu128);
        n.shl1_assign();
        assert_eq!(n, n_shl1);
    }

    #[test]
    fn shl_vartime() {
        let one = BoxedUint::one_with_precision(128);

        assert_eq!(BoxedUint::from(2u8), one.shl_vartime(1).unwrap());
        assert_eq!(BoxedUint::from(4u8), one.shl_vartime(2).unwrap());
        assert_eq!(
            BoxedUint::from(0x80000000000000000u128),
            one.shl_vartime(67).unwrap()
        );
    }
}
