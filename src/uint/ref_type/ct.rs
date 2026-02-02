//! Constant-time support: impls of `Ct*` traits and constant-time `const fn` operations.

use super::UintRef;
use crate::{Choice, CtAssign, CtEq};
use ctutils::CtLt;

impl CtAssign for UintRef {
    #[inline]
    fn ct_assign(&mut self, other: &Self, choice: Choice) {
        debug_assert_eq!(self.bits_precision(), other.bits_precision());
        self.limbs.ct_assign(&other.limbs, choice);
    }
}

// Note: special impl with implicit widening
impl<RHS: AsRef<UintRef>> CtEq<RHS> for UintRef {
    #[inline]
    fn ct_eq(&self, other: &RHS) -> Choice {
        let rhs = other.as_ref();
        let overlap = if self.nlimbs() < rhs.nlimbs() {
            self.nlimbs()
        } else {
            rhs.nlimbs()
        };
        let (lhs, lhs_over) = self.split_at(overlap);
        let (rhs, rhs_over) = rhs.split_at(overlap);
        lhs.limbs
            .ct_eq(&rhs.limbs)
            .and(lhs_over.is_zero())
            .and(rhs_over.is_zero())
    }
}

impl CtLt for UintRef {
    #[inline]
    fn ct_lt(&self, other: &Self) -> Choice {
        Self::lt(self, other)
    }
}
