//! [`BoxedUint`] addition operations.

use crate::{BoxedUint, CheckedAdd, Limb, Uint, Wrapping, WrappingAdd, Zero, U128, U64};
use core::ops::{Add, AddAssign};
use subtle::{Choice, ConditionallySelectable, CtOption};

impl BoxedUint {
    /// Computes `a + b + carry`, returning the result along with the new carry.
    #[inline(always)]
    pub fn adc(&self, rhs: &Self, carry: Limb) -> (Self, Limb) {
        Self::fold_limbs(self, rhs, carry, |a, b, c| a.adc(b, c))
    }

    /// Computes `a + b + carry` in-place, returning the new carry.
    ///
    /// Panics if `rhs` has a larger precision than `self`.
    #[inline]
    pub fn adc_assign(&mut self, rhs: impl AsRef<[Limb]>, mut carry: Limb) -> Limb {
        debug_assert!(self.bits_precision() <= (rhs.as_ref().len() as u32 * Limb::BITS));

        for i in 0..self.nlimbs() {
            let (limb, b) = self.limbs[i].adc(*rhs.as_ref().get(i).unwrap_or(&Limb::ZERO), carry);
            self.limbs[i] = limb;
            carry = b;
        }

        carry
    }

    /// Perform wrapping addition, discarding overflow.
    pub fn wrapping_add(&self, rhs: &Self) -> Self {
        self.adc(rhs, Limb::ZERO).0
    }

    /// Perform in-place wrapping addition, returning the truthy value as the second element of the
    /// tuple if an overflow has occurred.
    pub(crate) fn conditional_adc_assign(&mut self, rhs: &Self, choice: Choice) -> Choice {
        debug_assert!(self.bits_precision() <= rhs.bits_precision());
        let mask = Limb::conditional_select(&Limb::ZERO, &Limb::MAX, choice);
        let mut carry = Limb::ZERO;

        for i in 0..self.nlimbs() {
            let masked_rhs = *rhs.limbs.get(i).unwrap_or(&Limb::ZERO) & mask;
            let (limb, c) = self.limbs[i].adc(masked_rhs, carry);
            self.limbs[i] = limb;
            carry = c;
        }

        Choice::from((carry.0 & 1) as u8)
    }
}

impl Add for BoxedUint {
    type Output = Self;

    fn add(self, rhs: Self) -> Self {
        self.add(&rhs)
    }
}

impl Add<&BoxedUint> for BoxedUint {
    type Output = Self;

    fn add(self, rhs: &Self) -> Self {
        Add::add(&self, rhs)
    }
}

impl Add<&BoxedUint> for &BoxedUint {
    type Output = BoxedUint;

    fn add(self, rhs: &BoxedUint) -> BoxedUint {
        self.checked_add(rhs)
            .expect("attempted to add with overflow")
    }
}

impl<const LIMBS: usize> Add<Uint<LIMBS>> for BoxedUint {
    type Output = BoxedUint;

    fn add(self, rhs: Uint<LIMBS>) -> BoxedUint {
        self.add(&rhs)
    }
}

impl<const LIMBS: usize> Add<&Uint<LIMBS>> for BoxedUint {
    type Output = BoxedUint;

    fn add(mut self, rhs: &Uint<LIMBS>) -> BoxedUint {
        self += rhs;
        self
    }
}

impl<const LIMBS: usize> Add<Uint<LIMBS>> for &BoxedUint {
    type Output = BoxedUint;

    fn add(self, rhs: Uint<LIMBS>) -> BoxedUint {
        self.clone().add(rhs)
    }
}

impl<const LIMBS: usize> Add<&Uint<LIMBS>> for &BoxedUint {
    type Output = BoxedUint;

    fn add(self, rhs: &Uint<LIMBS>) -> BoxedUint {
        self.clone().add(rhs)
    }
}

impl<const LIMBS: usize> AddAssign<Uint<LIMBS>> for BoxedUint {
    fn add_assign(&mut self, rhs: Uint<LIMBS>) {
        *self += &rhs;
    }
}

impl<const LIMBS: usize> AddAssign<&Uint<LIMBS>> for BoxedUint {
    fn add_assign(&mut self, rhs: &Uint<LIMBS>) {
        let carry = self.adc_assign(rhs.as_limbs(), Limb::ZERO);
        assert_eq!(carry.0, 0, "attempted to add with overflow");
    }
}

impl AddAssign<Wrapping<BoxedUint>> for Wrapping<BoxedUint> {
    fn add_assign(&mut self, other: Wrapping<BoxedUint>) {
        self.0.adc_assign(&other.0, Limb::ZERO);
    }
}

impl AddAssign<&Wrapping<BoxedUint>> for Wrapping<BoxedUint> {
    fn add_assign(&mut self, other: &Wrapping<BoxedUint>) {
        self.0.adc_assign(&other.0, Limb::ZERO);
    }
}

impl CheckedAdd for BoxedUint {
    fn checked_add(&self, rhs: &Self) -> CtOption<Self> {
        let (result, carry) = self.adc(rhs, Limb::ZERO);
        CtOption::new(result, carry.is_zero())
    }
}

impl WrappingAdd for BoxedUint {
    fn wrapping_add(&self, v: &Self) -> Self {
        self.wrapping_add(v)
    }
}

macro_rules! impl_add_primitive {
    ($($primitive:ty),+) => {
        $(
            impl Add<$primitive> for BoxedUint {
                type Output = BoxedUint;

                #[inline]
                fn add(self, rhs: $primitive) -> BoxedUint {
                     self + U64::from(rhs)
                }
            }

            impl Add<$primitive> for &BoxedUint {
                type Output = BoxedUint;

                #[inline]
                fn add(self, rhs: $primitive) -> BoxedUint {
                     self + U64::from(rhs)
                }
            }

            impl AddAssign<$primitive> for BoxedUint {
                fn add_assign(&mut self, rhs: $primitive) {
                    *self += U64::from(rhs);
                }
            }
        )+
    };
}

impl_add_primitive!(u8, u16, u32, u64);

impl Add<u128> for BoxedUint {
    type Output = BoxedUint;

    #[inline]
    fn add(self, rhs: u128) -> BoxedUint {
        self + U128::from(rhs)
    }
}

impl Add<u128> for &BoxedUint {
    type Output = BoxedUint;

    #[inline]
    fn add(self, rhs: u128) -> BoxedUint {
        self + U128::from(rhs)
    }
}

impl AddAssign<u128> for BoxedUint {
    fn add_assign(&mut self, rhs: u128) {
        *self += U128::from(rhs);
    }
}

#[cfg(test)]
#[allow(clippy::unwrap_used)]
mod tests {
    use super::{BoxedUint, CheckedAdd, Limb};

    #[test]
    fn adc_no_carry() {
        let (res, carry) = BoxedUint::zero().adc(&BoxedUint::one(), Limb::ZERO);
        assert_eq!(res, BoxedUint::one());
        assert_eq!(carry, Limb::ZERO);
    }

    #[test]
    fn adc_with_carry() {
        let (res, carry) = BoxedUint::max(Limb::BITS).adc(&BoxedUint::one(), Limb::ZERO);
        assert_eq!(res, BoxedUint::zero());
        assert_eq!(carry, Limb::ONE);
    }

    #[test]
    fn add_with_u32_rhs() {
        let a = BoxedUint::from(1u64);
        let b = a + u32::MAX;
        assert_eq!(b, BoxedUint::from(0x100000000u64));
    }

    #[test]
    fn checked_add_ok() {
        let result = BoxedUint::zero().checked_add(&BoxedUint::one());
        assert_eq!(result.unwrap(), BoxedUint::one());
    }

    #[test]
    fn checked_add_overflow() {
        let result = BoxedUint::max(Limb::BITS).checked_add(&BoxedUint::one());
        assert!(!bool::from(result.is_some()));
    }
}
