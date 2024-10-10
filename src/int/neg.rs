//! [`Int`] negation operation.

use crate::int::Int;
use crate::WrappingNeg;

impl<const LIMBS: usize> Int<LIMBS> {
    /// Perform wrapping negation.
    pub fn wrapping_neg(&self) -> Self {
        Self {
            is_negative: !self.is_negative & !self.is_zero(),
            magnitude: self.magnitude,
        }
    }
}

impl<const LIMBS: usize> WrappingNeg for Int<LIMBS> {
    #[inline]
    fn wrapping_neg(&self) -> Self {
        self.wrapping_neg()
    }
}
