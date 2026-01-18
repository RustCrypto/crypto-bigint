//! [`BoxedUint`] addition operations.

use crate::{
    Add, AddAssign, BoxedUint, CheckedAdd, Choice, CtOption, CtSelect, Limb, Resize, U64, U128,
    Uint, Wrapping, WrappingAdd,
};
use core::cmp;
use ctutils::CtEq;

impl BoxedUint {
    /// Computes `self + rhs + carry`, returning the result along with the new carry.
    #[deprecated(since = "0.7.0", note = "please use `carrying_add` instead")]
    #[must_use]
    pub fn adc(&self, rhs: &Self, carry: Limb) -> (Self, Limb) {
        self.carrying_add(rhs, carry)
    }

    /// Computes `self + rhs + carry`, returning the result along with the new carry.
    #[inline(always)]
    #[must_use]
    pub fn carrying_add(&self, rhs: &Self, carry: Limb) -> (Self, Limb) {
        Self::fold_limbs(self, rhs, carry, Limb::carrying_add)
    }

    /// Computes `self + rhs + carry` in-place, returning the new carry.
    ///
    /// # Panics
    /// - if `rhs` has a larger precision than `self`.
    #[deprecated(since = "0.7.0", note = "please use `carrying_add_assign` instead")]
    pub fn adc_assign(&mut self, rhs: impl AsRef<[Limb]>, carry: Limb) -> Limb {
        self.carrying_add_assign(rhs, carry)
    }

    /// Computes `self + rhs + carry` in-place, returning the new carry.
    ///
    /// # Panics
    /// - if `rhs` has a larger precision than `self`.
    #[inline]
    pub fn carrying_add_assign(&mut self, rhs: impl AsRef<[Limb]>, mut carry: Limb) -> Limb {
        debug_assert!(self.bits_precision() >= (rhs.as_ref().len() as u32 * Limb::BITS));

        for i in 0..self.nlimbs() {
            let (limb, b) =
                self.limbs[i].carrying_add(*rhs.as_ref().get(i).unwrap_or(&Limb::ZERO), carry);
            self.limbs[i] = limb;
            carry = b;
        }

        carry
    }

    /// Computes `self + rhs`, returning a result which is concatenated with the overflow limb which
    /// would be returned if `carrying_add` were called with the same operands.
    #[must_use]
    pub fn concatenating_add(&self, rhs: &Self) -> Self {
        // Create a copy of `self` widened to one limb larger than the largest of `self` and `rhs`
        let nlimbs = cmp::max(self.nlimbs(), rhs.nlimbs()) + 1;
        let mut ret = self.resize(nlimbs as u32 * Limb::BITS);

        // Overflow should always be zero here because we added a zero limb to `self` in `ret`
        let _overflow = ret.carrying_add_assign(rhs, Limb::ZERO);
        debug_assert_eq!(_overflow, Limb::ZERO);
        ret
    }

    /// Computes `self + rhs`, returning a tuple of the sum along with a [`Choice`] which indicates
    /// whether an overflow occurred.
    ///
    /// If an overflow occurred, then the wrapped value is returned.
    #[must_use]
    pub fn overflowing_add(&self, rhs: &Self) -> (Self, Choice) {
        let (ret, overflow) = self.carrying_add(rhs, Limb::ZERO);
        (ret, overflow.ct_ne(&Limb::ZERO))
    }

    /// Perform wrapping addition, discarding overflow.
    #[must_use]
    pub fn wrapping_add(&self, rhs: &Self) -> Self {
        self.carrying_add(rhs, Limb::ZERO).0
    }

    /// Perform in-place wrapping addition, returning the truthy value as the second element of the
    /// tuple if an overflow has occurred.
    pub(crate) fn conditional_carrying_add_assign(&mut self, rhs: &Self, choice: Choice) -> Choice {
        debug_assert!(self.bits_precision() <= rhs.bits_precision());
        let mask = Limb::ZERO.ct_select(&Limb::MAX, choice);
        let mut carry = Limb::ZERO;

        for i in 0..self.nlimbs() {
            let masked_rhs = *rhs.limbs.get(i).unwrap_or(&Limb::ZERO) & mask;
            let (limb, c) = self.limbs[i].carrying_add(masked_rhs, carry);
            self.limbs[i] = limb;
            carry = c;
        }

        carry.lsb_to_choice()
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

impl Add<BoxedUint> for &BoxedUint {
    type Output = BoxedUint;

    fn add(self, rhs: BoxedUint) -> BoxedUint {
        Add::add(self, &rhs)
    }
}

impl Add<&BoxedUint> for &BoxedUint {
    type Output = BoxedUint;

    fn add(self, rhs: &BoxedUint) -> BoxedUint {
        self.checked_add(rhs)
            .expect("attempted to add with overflow")
    }
}

impl AddAssign<BoxedUint> for BoxedUint {
    fn add_assign(&mut self, rhs: BoxedUint) {
        self.add_assign(&rhs);
    }
}

impl AddAssign<&BoxedUint> for BoxedUint {
    fn add_assign(&mut self, rhs: &BoxedUint) {
        let carry = self.carrying_add_assign(rhs, Limb::ZERO);
        assert!(carry.is_zero().to_bool(), "attempted to add with overflow");
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
        let carry = self.carrying_add_assign(rhs.as_limbs(), Limb::ZERO);
        assert_eq!(carry.0, 0, "attempted to add with overflow");
    }
}

impl AddAssign<Wrapping<BoxedUint>> for Wrapping<BoxedUint> {
    fn add_assign(&mut self, other: Wrapping<BoxedUint>) {
        self.0.carrying_add_assign(&other.0, Limb::ZERO);
    }
}

impl AddAssign<&Wrapping<BoxedUint>> for Wrapping<BoxedUint> {
    fn add_assign(&mut self, other: &Wrapping<BoxedUint>) {
        self.0.carrying_add_assign(&other.0, Limb::ZERO);
    }
}

impl CheckedAdd for BoxedUint {
    fn checked_add(&self, rhs: &Self) -> CtOption<Self> {
        let (result, carry) = self.carrying_add(rhs, Limb::ZERO);
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
    use crate::Resize;

    #[test]
    fn add_assign() {
        let mut h = BoxedUint::one().resize(1024);
        h += BoxedUint::one();
    }

    #[test]
    fn add_with_u32_rhs() {
        let a = BoxedUint::from(1u64);
        let b = a + u32::MAX;
        assert_eq!(b, BoxedUint::from(0x100000000u64));
    }

    #[test]
    fn carrying_add_no_carry() {
        let (res, carry) = BoxedUint::zero().carrying_add(&BoxedUint::one(), Limb::ZERO);
        assert_eq!(res, BoxedUint::one());
        assert_eq!(carry, Limb::ZERO);
    }

    #[test]
    fn carrying_add_with_carry() {
        let (res, carry) = BoxedUint::max(Limb::BITS).carrying_add(&BoxedUint::one(), Limb::ZERO);
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

    #[test]
    fn concatenating_add() {
        let result = BoxedUint::max(Limb::BITS).concatenating_add(&BoxedUint::one());
        assert_eq!(result.as_limbs(), &[Limb::ZERO, Limb::ONE]);
    }

    #[test]
    fn overflowing_add() {
        let one = BoxedUint::one();
        let (ret, overflow) = one.overflowing_add(&one);
        assert_eq!(ret, &one + &one);
        assert!(!overflow.to_bool());

        let (ret, overflow) = BoxedUint::max(Limb::BITS).overflowing_add(&one);
        assert!(ret.is_zero().to_bool());
        assert!(overflow.to_bool());
    }
}
