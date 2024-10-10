use subtle::{ConditionallySelectable, ConstantTimeLess};

use crate::int::Int;

impl<const LIMBS: usize> Int<LIMBS> {
    /// Given two [`Int`]s, return a tuple, containing in order:
    /// - the one with the greatest absolute value, and
    /// - the one with the smallest absolute value.
    ///
    /// When both elements have the same size, their order is maintained.
    pub(crate) fn abs_max_min(&self, rhs: &Self) -> (Self, Self) {
        let swap = self.magnitude.ct_lt(&rhs.magnitude);
        let greatest = Int::conditional_select(self, rhs, swap);
        let smallest = Int::conditional_select(rhs, self, swap);
        (greatest, smallest)
    }
}
