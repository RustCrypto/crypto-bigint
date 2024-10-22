//! [`Int`] bitwise XOR operations.

use core::ops::{BitXor, BitXorAssign};

use subtle::{Choice, CtOption};

use crate::{Uint, Wrapping};

use super::Int;

impl<const LIMBS: usize> Int<LIMBS> {
    /// Computes bitwise `a ^ b`.
    #[inline(always)]
    pub const fn bitxor(&self, rhs: &Self) -> Self {
        Self(Uint::bitxor(&self.0, &rhs.0))
    }

    /// Perform wrapping bitwise `XOR`.
    ///
    /// There's no way wrapping could ever happen.
    /// This function exists so that all operations are accounted for in the wrapping operations
    pub const fn wrapping_xor(&self, rhs: &Self) -> Self {
        self.bitxor(rhs)
    }

    /// Perform checked bitwise `XOR`, returning a [`CtOption`] which `is_some` always
    pub fn checked_xor(&self, rhs: &Self) -> CtOption<Self> {
        let result = self.bitxor(rhs);
        CtOption::new(result, Choice::from(1))
    }
}

impl<const LIMBS: usize> BitXor for Int<LIMBS> {
    type Output = Self;

    fn bitxor(self, rhs: Self) -> Int<LIMBS> {
        self.bitxor(&rhs)
    }
}

impl<const LIMBS: usize> BitXor<&Int<LIMBS>> for Int<LIMBS> {
    type Output = Int<LIMBS>;

    #[allow(clippy::needless_borrow)]
    fn bitxor(self, rhs: &Int<LIMBS>) -> Int<LIMBS> {
        (&self).bitxor(rhs)
    }
}

impl<const LIMBS: usize> BitXor<Int<LIMBS>> for &Int<LIMBS> {
    type Output = Int<LIMBS>;

    fn bitxor(self, rhs: Int<LIMBS>) -> Int<LIMBS> {
        self.bitxor(&rhs)
    }
}

impl<const LIMBS: usize> BitXor<&Int<LIMBS>> for &Int<LIMBS> {
    type Output = Int<LIMBS>;

    fn bitxor(self, rhs: &Int<LIMBS>) -> Int<LIMBS> {
        self.bitxor(rhs)
    }
}

impl<const LIMBS: usize> BitXorAssign for Int<LIMBS> {
    fn bitxor_assign(&mut self, other: Self) {
        *self = *self ^ other;
    }
}

impl<const LIMBS: usize> BitXorAssign<&Int<LIMBS>> for Int<LIMBS> {
    fn bitxor_assign(&mut self, other: &Self) {
        *self = *self ^ other;
    }
}

impl<const LIMBS: usize> BitXor for Wrapping<Int<LIMBS>> {
    type Output = Self;

    fn bitxor(self, rhs: Self) -> Wrapping<Int<LIMBS>> {
        Wrapping(self.0.bitxor(&rhs.0))
    }
}

impl<const LIMBS: usize> BitXor<&Wrapping<Int<LIMBS>>> for Wrapping<Int<LIMBS>> {
    type Output = Wrapping<Int<LIMBS>>;

    fn bitxor(self, rhs: &Wrapping<Int<LIMBS>>) -> Wrapping<Int<LIMBS>> {
        Wrapping(self.0.bitxor(&rhs.0))
    }
}

impl<const LIMBS: usize> BitXor<Wrapping<Int<LIMBS>>> for &Wrapping<Int<LIMBS>> {
    type Output = Wrapping<Int<LIMBS>>;

    fn bitxor(self, rhs: Wrapping<Int<LIMBS>>) -> Wrapping<Int<LIMBS>> {
        Wrapping(self.0.bitxor(&rhs.0))
    }
}

impl<const LIMBS: usize> BitXor<&Wrapping<Int<LIMBS>>> for &Wrapping<Int<LIMBS>> {
    type Output = Wrapping<Int<LIMBS>>;

    fn bitxor(self, rhs: &Wrapping<Int<LIMBS>>) -> Wrapping<Int<LIMBS>> {
        Wrapping(self.0.bitxor(&rhs.0))
    }
}

impl<const LIMBS: usize> BitXorAssign for Wrapping<Int<LIMBS>> {
    fn bitxor_assign(&mut self, other: Self) {
        *self = *self ^ other;
    }
}

impl<const LIMBS: usize> BitXorAssign<&Wrapping<Int<LIMBS>>> for Wrapping<Int<LIMBS>> {
    fn bitxor_assign(&mut self, other: &Self) {
        *self = *self ^ other;
    }
}
