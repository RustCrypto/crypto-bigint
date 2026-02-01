//! [`BoxedUint`] multiplication operations.

use crate::{
    BoxedUint, CheckedMul, Choice, ConcatenatingMul, CtOption, Limb, Mul, MulAssign, Uint, UintRef,
    Wrapping, WrappingMul,
};

mod helper;
pub(crate) use helper::BoxedMultiplier;

impl BoxedUint {
    /// Multiply `self` by `rhs`.
    ///
    /// Returns a widened output with a limb count equal to the sums of the input limb counts.
    #[must_use]
    pub fn mul(&self, rhs: &Self) -> Self {
        self.wrapping_mul_carry(rhs.as_uint_ref(), self.nlimbs() + rhs.nlimbs())
            .0
    }

    /// Multiply `self` by `rhs`.
    ///
    /// Returns a widened output with a limb count equal to the sums of the input limb counts.
    #[must_use]
    pub(crate) fn mul_unsigned<const LIMBS: usize>(&self, rhs: &Uint<LIMBS>) -> Self {
        self.wrapping_mul_carry(rhs.as_uint_ref(), self.nlimbs() + LIMBS)
            .0
    }

    /// Perform wrapping multiplication, wrapping to the width of `self`.
    #[must_use]
    pub fn wrapping_mul(&self, rhs: &Self) -> Self {
        self.wrapping_mul_carry(rhs.as_uint_ref(), self.nlimbs()).0
    }

    /// Multiply `self` by `rhs`, wrapping to the width of `self`.
    /// Returns `CtOption::None` if the result overflowed the precision of `self`.
    #[must_use]
    pub fn checked_mul(&self, rhs: &Self) -> CtOption<Self> {
        let (res, overflow) = self.overflowing_mul(rhs.as_uint_ref(), self.nlimbs());
        CtOption::new(res, overflow.not())
    }

    /// Perform saturating multiplication, returning `MAX` on overflow.
    #[must_use]
    pub fn saturating_mul(&self, rhs: &Self) -> Self {
        let (mut res, overflow) = self.overflowing_mul(rhs.as_uint_ref(), self.nlimbs());
        res.as_mut_uint_ref().conditional_set_max(overflow);
        res
    }

    /// Multiply `self` by `rhs`, wrapping to the width of `self`.
    /// Returns a `Choice` indicating if the result overflowed the precision of `self`.
    #[inline(always)]
    #[must_use]
    pub(crate) fn overflowing_mul(&self, rhs: &UintRef, size: usize) -> (Self, Choice) {
        let mut limbs = vec![Limb::ZERO; size];
        let overflow = self
            .as_uint_ref()
            .overflowing_mul(rhs, UintRef::new_mut(&mut limbs));
        (limbs.into(), overflow)
    }

    #[inline(always)]
    fn wrapping_mul_carry(&self, rhs: &UintRef, size: usize) -> (Self, Limb) {
        let mut limbs = vec![Limb::ZERO; size];
        let carry = self
            .as_uint_ref()
            .wrapping_mul(rhs, UintRef::new_mut(limbs.as_mut_slice()));
        (limbs.into(), carry)
    }

    /// Multiply `self` by itself.
    #[must_use]
    pub fn square(&self) -> Self {
        self.wrapping_square_carry(self.nlimbs() * 2).0
    }

    /// Multiply `self` by itself, wrapping to the width of `self`.
    #[must_use]
    pub fn wrapping_square(&self) -> Self {
        self.wrapping_square_carry(self.nlimbs()).0
    }

    /// Multiply `self` by itself, wrapping to the width of `self`.
    /// Returns `CtOption::None` if the result overflowed the precision of `self`.
    #[must_use]
    pub fn checked_square(&self) -> CtOption<Self> {
        let (res, overflow) = self.overflowing_square(self.nlimbs());
        CtOption::new(res, overflow.not())
    }

    /// Perform saturating squaring, returning `MAX` on overflow.
    #[must_use]
    pub fn saturating_square(&self) -> Self {
        let (mut res, overflow) = self.overflowing_square(self.nlimbs());
        res.as_mut_uint_ref().conditional_set_max(overflow);
        res
    }

    /// Multiply `self` by itself, wrapping to the width of `self`.
    /// Returns a `Choice` indicating if the result overflowed the precision of `self`.
    #[inline(always)]
    #[must_use]
    pub(crate) fn overflowing_square(&self, size: usize) -> (Self, Choice) {
        let mut limbs = vec![Limb::ZERO; size];
        let overflow = self
            .as_uint_ref()
            .overflowing_square(UintRef::new_mut(&mut limbs));
        (limbs.into(), overflow)
    }

    /// Multiply `self` by itself, wrapping to the width of `self`.
    /// Returns a pair of the wrapped product and a Limb representing the carry.
    #[inline(always)]
    #[must_use]
    fn wrapping_square_carry(&self, size: usize) -> (Self, Limb) {
        let mut limbs = vec![Limb::ZERO; size];
        let carry = self
            .as_uint_ref()
            .wrapping_square(UintRef::new_mut(limbs.as_mut_slice()));
        (limbs.into(), carry)
    }
}

impl CheckedMul for BoxedUint {
    fn checked_mul(&self, rhs: &BoxedUint) -> CtOption<Self> {
        self.checked_mul(rhs)
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
        BoxedUint::mul(self, rhs)
    }
}

impl MulAssign<BoxedUint> for BoxedUint {
    fn mul_assign(&mut self, rhs: BoxedUint) {
        self.mul_assign(&rhs);
    }
}

impl MulAssign<&BoxedUint> for BoxedUint {
    fn mul_assign(&mut self, rhs: &BoxedUint) {
        *self = BoxedUint::mul(self, rhs);
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

impl ConcatenatingMul for BoxedUint {
    type Output = Self;

    #[inline]
    fn concatenating_mul(&self, rhs: BoxedUint) -> Self {
        self.mul(&rhs)
    }
}

impl ConcatenatingMul<&BoxedUint> for BoxedUint {
    type Output = Self;

    #[inline]
    fn concatenating_mul(&self, rhs: &BoxedUint) -> Self {
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
    use crate::{BoxedUint, CheckedMul, ConcatenatingMul, Resize, WrappingMul};

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
                let expected = BoxedUint::from(u64::from(a_int) * u64::from(b_int));
                assert_eq!(actual, expected);
            }
        }
    }

    #[cfg(feature = "rand_core")]
    #[test]
    fn mul_cmp() {
        use crate::{RandomBits, Resize};
        use rand_core::SeedableRng;
        let mut rng = chacha20::ChaCha8Rng::seed_from_u64(1);
        let bits = if cfg!(miri) { 512 } else { 4096 };
        let rounds = if cfg!(miri) { 10 } else { 50 };

        for i in 0..rounds {
            let a = BoxedUint::random_bits(&mut rng, bits);
            assert_eq!(a.mul(&a), a.square(), "a={a}, i={i}");
            assert_eq!(a.wrapping_mul(&a), a.wrapping_square(), "a={a}, i={i}");
            assert_eq!(a.saturating_mul(&a), a.saturating_square(), "a={a}, i={i}");
        }

        for i in 0..rounds {
            let a = BoxedUint::random_bits(&mut rng, bits);
            let b = BoxedUint::random_bits(&mut rng, bits + 64);
            let expect = &a * &b;
            assert_eq!(&b * a.clone(), expect, "a={a}, b={b}, i={i}");
            assert_eq!(
                ConcatenatingMul::concatenating_mul(&b, &a),
                expect,
                "a={a}, b={b}, i={i}"
            );
            assert_eq!(
                WrappingMul::wrapping_mul(&a, &b),
                expect.clone().resize_unchecked(a.bits_precision()),
                "a={a}, b={b}, i={i}"
            );
            assert_eq!(
                WrappingMul::wrapping_mul(&b, &a),
                expect.clone().resize_unchecked(b.bits_precision()),
                "a={a}, b={b}, i={i}"
            );
        }
    }

    #[test]
    fn checked_mul_cmp() {
        let n = BoxedUint::max(64)
            .resize_unchecked(256)
            .wrapping_add(&BoxedUint::one());
        let n2 = n.checked_square();
        assert!(n2.is_some().to_bool());
        let n2_c = CheckedMul::checked_mul(&n, &n);
        assert_eq!(n2.clone().into_option(), n2_c.into_option());
        let n2 = n2.unwrap();

        let n4 = n2.checked_square();
        assert!(n4.is_none().to_bool());
        let n4_c = CheckedMul::checked_mul(&n2, &n2);
        assert!(n4_c.is_none().to_bool());

        let z = BoxedUint::zero_with_precision(256);
        let z2 = z.checked_square();
        assert!(z2.is_some().to_bool());
        let z2_c = CheckedMul::checked_mul(&z, &z);
        assert_eq!(z2.into_option(), z2_c.into_option());

        let m = BoxedUint::max(256);
        assert!(m.checked_square().is_none().to_bool());
        assert!(CheckedMul::checked_mul(&m, &m).is_none().to_bool());
    }
}
