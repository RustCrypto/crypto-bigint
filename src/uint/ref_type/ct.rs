//! Constant-time support: impls of `Ct*` traits and constant-time `const fn` operations.

use super::UintRef;
use crate::{Choice, CtAssign, CtEq, CtLt};

impl CtAssign for UintRef {
    #[inline]
    fn ct_assign(&mut self, other: &Self, choice: Choice) {
        debug_assert_eq!(self.bits_precision(), other.bits_precision());
        self.limbs.ct_assign(&other.limbs, choice);
    }
}

impl CtEq for UintRef {
    #[inline]
    fn ct_eq(&self, other: &Self) -> Choice {
        self.limbs.ct_eq(&other.limbs)
    }
}

impl CtLt for UintRef {
    #[inline]
    fn ct_lt(&self, other: &Self) -> Choice {
        Self::lt(self, other)
    }
}
