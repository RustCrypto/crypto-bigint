//! [`BoxedUint`] addition operations.

use core::ops::{Add, AddAssign};

use crate::{BoxedUint, CheckedAdd, Limb, Wrapping, Zero};
use subtle::{Choice, CtOption};

impl BoxedUint {
    /// Computes `a + b + carry`, returning the result along with the new carry.
    #[inline(always)]
    pub fn adc(&self, rhs: &Self, carry: Limb) -> (Self, Limb) {
        Self::fold_limbs(self, rhs, carry, |a, b, c| a.adc(b, c))
    }

    /// Perform wrapping addition, discarding overflow.
    pub fn wrapping_add(&self, rhs: &Self) -> Self {
        self.adc(rhs, Limb::ZERO).0
    }

    /// Perform wrapping addition, returning the truthy value as the second element of the tuple
    /// if an overflow has occurred.
    pub(crate) fn conditional_wrapping_add(&self, rhs: &Self, choice: Choice) -> (Self, Choice) {
        let actual_rhs = Self::conditional_select(
            &Self::zero_with_precision(rhs.bits_precision()),
            rhs,
            choice,
        );
        let (sum, carry) = self.adc(&actual_rhs, Limb::ZERO);
        (sum, Choice::from((carry.0 & 1) as u8))
    }
}

impl CheckedAdd<&BoxedUint> for BoxedUint {
    type Output = Self;

    fn checked_add(&self, rhs: &Self) -> CtOption<Self> {
        let (result, carry) = self.adc(rhs, Limb::ZERO);
        CtOption::new(result, carry.is_zero())
    }
}

impl Add<Wrapping<BoxedUint>> for Wrapping<BoxedUint> {
    type Output = Self;

    fn add(self, rhs: Wrapping<BoxedUint>) -> Wrapping<BoxedUint> {
        Wrapping(self.0.wrapping_add(&rhs.0))
    }
}

impl Add<&Wrapping<BoxedUint>> for Wrapping<BoxedUint> {
    type Output = Self;

    fn add(self, rhs: &Wrapping<BoxedUint>) -> Wrapping<BoxedUint> {
        Wrapping(self.0.wrapping_add(&rhs.0))
    }
}

impl Add<Wrapping<BoxedUint>> for &Wrapping<BoxedUint> {
    type Output = Wrapping<BoxedUint>;

    fn add(self, rhs: Wrapping<BoxedUint>) -> Wrapping<BoxedUint> {
        Wrapping(self.0.wrapping_add(&rhs.0))
    }
}

impl Add<&Wrapping<BoxedUint>> for &Wrapping<BoxedUint> {
    type Output = Wrapping<BoxedUint>;

    fn add(self, rhs: &Wrapping<BoxedUint>) -> Wrapping<BoxedUint> {
        Wrapping(self.0.wrapping_add(&rhs.0))
    }
}

impl AddAssign<Wrapping<BoxedUint>> for Wrapping<BoxedUint> {
    fn add_assign(&mut self, other: Wrapping<BoxedUint>) {
        *self = Wrapping(self.0.wrapping_add(&other.0));
    }
}

impl AddAssign<&Wrapping<BoxedUint>> for Wrapping<BoxedUint> {
    fn add_assign(&mut self, other: &Wrapping<BoxedUint>) {
        *self = Wrapping(self.0.wrapping_add(&other.0));
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
