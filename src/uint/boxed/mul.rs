//! [`BoxedUint`] multiplication operations.

use crate::{
    uint::mul::{
        karatsuba::{karatsuba_mul_limbs, karatsuba_square_limbs, KARATSUBA_MIN_STARTING_LIMBS},
        mul_limbs, square_limbs,
    },
    BoxedUint, CheckedMul, Limb, WideningMul, Wrapping, WrappingMul, Zero,
};
use core::ops::{Mul, MulAssign};
use subtle::{Choice, CtOption};

impl BoxedUint {
    /// Multiply `self` by `rhs`.
    ///
    /// Returns a widened output with a limb count equal to the sums of the input limb counts.
    pub fn mul(&self, rhs: &Self) -> Self {
        let size = self.nlimbs() + rhs.nlimbs();
        let overlap = self.nlimbs().min(rhs.nlimbs());

        if self.nlimbs().min(rhs.nlimbs()) >= KARATSUBA_MIN_STARTING_LIMBS {
            let mut limbs = vec![Limb::ZERO; size + overlap * 2];
            let (out, scratch) = limbs.as_mut_slice().split_at_mut(size);
            karatsuba_mul_limbs(&self.limbs, &rhs.limbs, out, scratch);
            limbs.truncate(size);
            return limbs.into();
        }

        let mut limbs = vec![Limb::ZERO; size];
        mul_limbs(&self.limbs, &rhs.limbs, &mut limbs);
        limbs.into()
    }

    /// Perform wrapping multiplication, wrapping to the width of `self`.
    pub fn wrapping_mul(&self, rhs: &Self) -> Self {
        self.mul(rhs).shorten(self.bits_precision())
    }

    /// Multiply `self` by itself.
    pub fn square(&self) -> Self {
        let size = self.nlimbs() * 2;

        if self.nlimbs() >= KARATSUBA_MIN_STARTING_LIMBS * 2 {
            let mut limbs = vec![Limb::ZERO; size * 2];
            let (out, scratch) = limbs.as_mut_slice().split_at_mut(size);
            karatsuba_square_limbs(&self.limbs, out, scratch);
            limbs.truncate(size);
            return limbs.into();
        }

        let mut limbs = vec![Limb::ZERO; size];
        square_limbs(&self.limbs, &mut limbs);
        limbs.into()
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

    #[cfg(feature = "rand_core")]
    #[test]
    fn mul_cmp() {
        use crate::RandomBits;
        use rand_core::SeedableRng;
        let mut rng = rand_chacha::ChaCha8Rng::seed_from_u64(1);

        for _ in 0..50 {
            let a = BoxedUint::random_bits(&mut rng, 4096);
            assert_eq!(a.mul(&a), a.square(), "a = {a}");
        }

        for _ in 0..50 {
            let a = BoxedUint::random_bits(&mut rng, 4096);
            let b = BoxedUint::random_bits(&mut rng, 5000);
            assert_eq!(a.mul(&b), b.mul(&a), "a={a}, b={b}");
        }
    }
}
