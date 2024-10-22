//! [`Int`] bitwise OR operations.

use core::ops::{BitOr, BitOrAssign};

use subtle::{Choice, CtOption};

use crate::{Uint, Wrapping};

use super::Int;

impl<const LIMBS: usize> Int<LIMBS> {
    /// Computes bitwise `a & b`.
    #[inline(always)]
    pub const fn bitor(&self, rhs: &Self) -> Self {
        Self(Uint::bitor(&self.0, &rhs.0))
    }

    /// Perform wrapping bitwise `OR`.
    ///
    /// There's no way wrapping could ever happen.
    /// This function exists so that all operations are accounted for in the wrapping operations
    pub const fn wrapping_or(&self, rhs: &Self) -> Self {
        self.bitor(rhs)
    }

    /// Perform checked bitwise `OR`, returning a [`CtOption`] which `is_some` always
    pub fn checked_or(&self, rhs: &Self) -> CtOption<Self> {
        let result = self.bitor(rhs);
        CtOption::new(result, Choice::from(1))
    }
}

impl<const LIMBS: usize> BitOr for Int<LIMBS> {
    type Output = Self;

    fn bitor(self, rhs: Self) -> Int<LIMBS> {
        self.bitor(&rhs)
    }
}

impl<const LIMBS: usize> BitOr<&Int<LIMBS>> for Int<LIMBS> {
    type Output = Int<LIMBS>;

    #[allow(clippy::needless_borrow)]
    fn bitor(self, rhs: &Int<LIMBS>) -> Int<LIMBS> {
        (&self).bitor(rhs)
    }
}

impl<const LIMBS: usize> BitOr<Int<LIMBS>> for &Int<LIMBS> {
    type Output = Int<LIMBS>;

    fn bitor(self, rhs: Int<LIMBS>) -> Int<LIMBS> {
        self.bitor(&rhs)
    }
}

impl<const LIMBS: usize> BitOr<&Int<LIMBS>> for &Int<LIMBS> {
    type Output = Int<LIMBS>;

    fn bitor(self, rhs: &Int<LIMBS>) -> Int<LIMBS> {
        self.bitor(rhs)
    }
}

impl<const LIMBS: usize> BitOrAssign for Int<LIMBS> {
    fn bitor_assign(&mut self, other: Self) {
        *self = *self | other;
    }
}

impl<const LIMBS: usize> BitOrAssign<&Int<LIMBS>> for Int<LIMBS> {
    fn bitor_assign(&mut self, other: &Self) {
        *self = *self | other;
    }
}

impl<const LIMBS: usize> BitOr for Wrapping<Int<LIMBS>> {
    type Output = Self;

    fn bitor(self, rhs: Self) -> Wrapping<Int<LIMBS>> {
        Wrapping(self.0.bitor(&rhs.0))
    }
}

impl<const LIMBS: usize> BitOr<&Wrapping<Int<LIMBS>>> for Wrapping<Int<LIMBS>> {
    type Output = Wrapping<Int<LIMBS>>;

    fn bitor(self, rhs: &Wrapping<Int<LIMBS>>) -> Wrapping<Int<LIMBS>> {
        Wrapping(self.0.bitor(&rhs.0))
    }
}

impl<const LIMBS: usize> BitOr<Wrapping<Int<LIMBS>>> for &Wrapping<Int<LIMBS>> {
    type Output = Wrapping<Int<LIMBS>>;

    fn bitor(self, rhs: Wrapping<Int<LIMBS>>) -> Wrapping<Int<LIMBS>> {
        Wrapping(self.0.bitor(&rhs.0))
    }
}

impl<const LIMBS: usize> BitOr<&Wrapping<Int<LIMBS>>> for &Wrapping<Int<LIMBS>> {
    type Output = Wrapping<Int<LIMBS>>;

    fn bitor(self, rhs: &Wrapping<Int<LIMBS>>) -> Wrapping<Int<LIMBS>> {
        Wrapping(self.0.bitor(&rhs.0))
    }
}

impl<const LIMBS: usize> BitOrAssign for Wrapping<Int<LIMBS>> {
    fn bitor_assign(&mut self, other: Self) {
        *self = *self | other;
    }
}

impl<const LIMBS: usize> BitOrAssign<&Wrapping<Int<LIMBS>>> for Wrapping<Int<LIMBS>> {
    fn bitor_assign(&mut self, other: &Self) {
        *self = *self | other;
    }
}
