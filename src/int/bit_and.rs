//! [`Int`] bitwise AND operations.

use core::ops::{BitAnd, BitAndAssign};

use subtle::{Choice, CtOption};

use crate::{Int, Limb, Uint, Wrapping};

impl<const LIMBS: usize> Int<LIMBS> {
    /// Computes bitwise `a & b`.
    #[inline(always)]
    pub const fn bitand(&self, rhs: &Self) -> Self {
        Self(Uint::bitand(&self.0, &rhs.0))
    }

    /// Perform bitwise `AND` between `self` and the given [`Limb`], performing the `AND` operation
    /// on every limb of `self`.
    pub const fn bitand_limb(&self, rhs: Limb) -> Self {
        Self(Uint::bitand_limb(&self.0, rhs))
    }

    /// Perform wrapping bitwise `AND`.
    ///
    /// There's no way wrapping could ever happen.
    /// This function exists so that all operations are accounted for in the wrapping operations
    pub const fn wrapping_and(&self, rhs: &Self) -> Self {
        self.bitand(rhs)
    }

    /// Perform checked bitwise `AND`, returning a [`CtOption`] which `is_some` always
    pub fn checked_and(&self, rhs: &Self) -> CtOption<Self> {
        let result = self.bitand(rhs);
        CtOption::new(result, Choice::from(1))
    }
}

impl<const LIMBS: usize> BitAnd for Int<LIMBS> {
    type Output = Self;

    fn bitand(self, rhs: Self) -> Int<LIMBS> {
        self.bitand(&rhs)
    }
}

impl<const LIMBS: usize> BitAnd<&Int<LIMBS>> for Int<LIMBS> {
    type Output = Int<LIMBS>;

    #[allow(clippy::needless_borrow)]
    fn bitand(self, rhs: &Int<LIMBS>) -> Int<LIMBS> {
        (&self).bitand(rhs)
    }
}

impl<const LIMBS: usize> BitAnd<Int<LIMBS>> for &Int<LIMBS> {
    type Output = Int<LIMBS>;

    fn bitand(self, rhs: Int<LIMBS>) -> Int<LIMBS> {
        self.bitand(&rhs)
    }
}

impl<const LIMBS: usize> BitAnd<&Int<LIMBS>> for &Int<LIMBS> {
    type Output = Int<LIMBS>;

    fn bitand(self, rhs: &Int<LIMBS>) -> Int<LIMBS> {
        self.bitand(rhs)
    }
}

impl<const LIMBS: usize> BitAndAssign for Int<LIMBS> {
    #[allow(clippy::assign_op_pattern)]
    fn bitand_assign(&mut self, other: Self) {
        *self = *self & other;
    }
}

impl<const LIMBS: usize> BitAndAssign<&Int<LIMBS>> for Int<LIMBS> {
    #[allow(clippy::assign_op_pattern)]
    fn bitand_assign(&mut self, other: &Self) {
        *self = *self & other;
    }
}

impl<const LIMBS: usize> BitAnd for Wrapping<Int<LIMBS>> {
    type Output = Self;

    fn bitand(self, rhs: Self) -> Wrapping<Int<LIMBS>> {
        Wrapping(self.0.bitand(&rhs.0))
    }
}

impl<const LIMBS: usize> BitAnd<&Wrapping<Int<LIMBS>>> for Wrapping<Int<LIMBS>> {
    type Output = Wrapping<Int<LIMBS>>;

    fn bitand(self, rhs: &Wrapping<Int<LIMBS>>) -> Wrapping<Int<LIMBS>> {
        Wrapping(self.0.bitand(&rhs.0))
    }
}

impl<const LIMBS: usize> BitAnd<Wrapping<Int<LIMBS>>> for &Wrapping<Int<LIMBS>> {
    type Output = Wrapping<Int<LIMBS>>;

    fn bitand(self, rhs: Wrapping<Int<LIMBS>>) -> Wrapping<Int<LIMBS>> {
        Wrapping(self.0.bitand(&rhs.0))
    }
}

impl<const LIMBS: usize> BitAnd<&Wrapping<Int<LIMBS>>> for &Wrapping<Int<LIMBS>> {
    type Output = Wrapping<Int<LIMBS>>;

    fn bitand(self, rhs: &Wrapping<Int<LIMBS>>) -> Wrapping<Int<LIMBS>> {
        Wrapping(self.0.bitand(&rhs.0))
    }
}

impl<const LIMBS: usize> BitAndAssign for Wrapping<Int<LIMBS>> {
    #[allow(clippy::assign_op_pattern)]
    fn bitand_assign(&mut self, other: Self) {
        *self = *self & other;
    }
}

impl<const LIMBS: usize> BitAndAssign<&Wrapping<Int<LIMBS>>> for Wrapping<Int<LIMBS>> {
    #[allow(clippy::assign_op_pattern)]
    fn bitand_assign(&mut self, other: &Self) {
        *self = *self & other;
    }
}
