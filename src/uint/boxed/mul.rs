//! [`BoxedUint`] multiplication operations.

use crate::{
    uint::mul::mul_limbs, BoxedUint, CheckedMul, Limb, WideningMul, Wrapping, WrappingMul, Zero,
};
use core::ops::{Mul, MulAssign};
use subtle::{Choice, CtOption};

impl BoxedUint {
    /// Multiply `self` by `rhs`.
    ///
    /// Returns a widened output with a limb count equal to the sums of the input limb counts.
    pub fn mul(&self, rhs: &Self) -> Self {
        let mut limbs = vec![0; self.nlimbs() + rhs.nlimbs()];
        mul_limbs(self.as_words(), rhs.as_words(), &mut limbs);
        limbs.into()
    }

    /// Perform wrapping multiplication, wrapping to the width of `self`.
    pub fn wrapping_mul(&self, rhs: &Self) -> Self {
        self.mul(rhs).shorten(self.bits_precision())
    }

    #[inline(never)]
    fn wrapping_mul_assign(&mut self, rhs: &Self) {
        *self = self.wrapping_mul(rhs);
    }

    /// Multiply `self` by itself.
    pub fn square(&self) -> Self {
        // TODO(tarcieri): more optimized implementation (shared with `Uint`?)
        self.mul(self)
    }
}

impl CheckedMul for BoxedUint {
    fn checked_mul(&self, rhs: &BoxedUint) -> CtOption<Self> {
        let product = self.mul(rhs);

        // Ensure high limbs are all zero
        let is_some = product.limbs[self.nlimbs()..]
            .iter()
            .fold(Choice::from(1), |choice, limb| choice & limb.is_zero());

        let mut limbs = product.limbs.into_vec();
        limbs.truncate(self.nlimbs());
        CtOption::new(limbs.into(), is_some)
    }
}

impl Mul<BoxedUint> for BoxedUint {
    type Output = BoxedUint;

    fn mul(self, rhs: BoxedUint) -> Self {
        BoxedUint::mul(&self, &rhs)
    }
}

impl Mul<&BoxedUint> for BoxedUint {
    type Output = BoxedUint;

    fn mul(self, rhs: &BoxedUint) -> Self {
        BoxedUint::mul(&self, rhs)
    }
}

impl Mul<BoxedUint> for &BoxedUint {
    type Output = BoxedUint;

    fn mul(self, rhs: BoxedUint) -> Self::Output {
        BoxedUint::mul(self, &rhs)
    }
}

impl Mul<&BoxedUint> for &BoxedUint {
    type Output = BoxedUint;

    fn mul(self, rhs: &BoxedUint) -> Self::Output {
        self.checked_mul(rhs)
            .expect("attempted to multiply with overflow")
    }
}

impl MulAssign<Wrapping<BoxedUint>> for Wrapping<BoxedUint> {
    fn mul_assign(&mut self, other: Wrapping<BoxedUint>) {
        *self = Wrapping(self.0.wrapping_mul(&other.0));
    }
}

impl MulAssign<&Wrapping<BoxedUint>> for Wrapping<BoxedUint> {
    fn mul_assign(&mut self, other: &Wrapping<BoxedUint>) {
        *self = Wrapping(self.0.wrapping_mul(&other.0));
    }
}

impl WideningMul for BoxedUint {
    type Output = Self;

    #[inline]
    fn widening_mul(&self, rhs: BoxedUint) -> Self {
        self.mul(&rhs)
    }
}

impl WideningMul<&BoxedUint> for BoxedUint {
    type Output = Self;

    #[inline]
    fn widening_mul(&self, rhs: &BoxedUint) -> Self {
        self.mul(rhs)
    }
}

impl WrappingMul for BoxedUint {
    fn wrapping_mul(&self, v: &Self) -> Self {
        self.wrapping_mul(v)
    }
}

#[cfg(test)]
mod tests {
    use crate::BoxedUint;

    #[test]
    fn mul_zero_and_one() {
        assert!(bool::from(
            BoxedUint::zero().mul(&BoxedUint::zero()).is_zero()
        ));
        assert!(bool::from(
            BoxedUint::zero().mul(&BoxedUint::one()).is_zero()
        ));
        assert!(bool::from(
            BoxedUint::one().mul(&BoxedUint::zero()).is_zero()
        ));
        assert_eq!(BoxedUint::one().mul(&BoxedUint::one()), BoxedUint::one());
    }

    #[test]
    fn mul_primes() {
        let primes: &[u32] = &[3, 5, 17, 257, 65537];

        for &a_int in primes {
            for &b_int in primes {
                let actual = BoxedUint::from(a_int).mul(&BoxedUint::from(b_int));
                let expected = BoxedUint::from(a_int as u64 * b_int as u64);
                assert_eq!(actual, expected);
            }
        }
    }
}
