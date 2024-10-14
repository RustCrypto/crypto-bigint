//! [`Int`] multiplication operations.

use subtle::{ConstantTimeEq, CtOption};

use crate::int::Int;
use crate::{CheckedMul, Uint, Zero};

impl<const LIMBS: usize, const RHS_LIMBS: usize> CheckedMul<Int<RHS_LIMBS>> for Int<LIMBS> {
    #[inline]
    fn checked_mul(&self, rhs: &Int<RHS_LIMBS>) -> CtOption<Self> {
        let (lo, hi) = self.magnitude.split_mul(&rhs.magnitude);
        let is_negative = (self.is_negative() ^ rhs.is_negative()) & lo.ct_ne(&Uint::ZERO);
        CtOption::new(Int::new_from_uint(is_negative.into(), lo), hi.is_zero())
    }
}
