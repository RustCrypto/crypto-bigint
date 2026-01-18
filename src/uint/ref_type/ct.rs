//! Constant-time support: impls of `Ct*` traits and constant-time `const fn` operations.

use super::UintRef;
use crate::{Choice, CtAssign, CtEq};

impl CtAssign for UintRef {
    #[inline]
    fn ct_assign(&mut self, other: &Self, choice: Choice) {
        debug_assert_eq!(self.bits_precision(), other.bits_precision());
        self.0.ct_assign(&other.0, choice);
    }
}

impl CtEq for UintRef {
    #[inline]
    fn ct_eq(&self, other: &Self) -> Choice {
        self.0.ct_eq(&other.0)
    }
}
