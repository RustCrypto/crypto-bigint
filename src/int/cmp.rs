//! [`Int`] comparisons.
//!
//! By default, these are all constant-time and use the `subtle` crate.

use subtle::{ConditionallySelectable, ConstantTimeLess};

use crate::int::Int;

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
}
