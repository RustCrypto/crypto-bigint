//! [`Int`] comparisons.
//!
//! By default, these are all constant-time and use the `subtle` crate.

use subtle::{Choice, ConditionallySelectable, ConstantTimeEq, ConstantTimeLess};

use crate::int::Int;
use crate::Uint;

impl<const LIMBS: usize> Int<LIMBS> {
    /// Given two [`Int`]s, return a tuple with the larger magnitude first.
    ///
    /// When both have the same magnitude, they are returned in the same order
    /// as they were provided.
    pub(crate) fn abs_max_min(&self, rhs: &Self) -> (Self, Self) {
        let swap = self.magnitude.ct_lt(&rhs.magnitude);
        let greatest = Int::conditional_select(self, rhs, swap);
        let smallest = Int::conditional_select(rhs, self, swap);
        (greatest, smallest)
    }

    #[inline]
    /// TODO: make this a const function?
    pub(crate) fn eq(lhs: &Self, rhs: &Self) -> Choice {
        Choice::from(Uint::eq(&lhs.magnitude, &rhs.magnitude))
            & Choice::ct_eq(&lhs.is_negative(), &rhs.is_negative())
    }
}

impl<const LIMBS: usize> ConstantTimeEq for Int<LIMBS> {
    #[inline]
    fn ct_eq(&self, other: &Self) -> Choice {
        Int::eq(self, other)
    }
}
