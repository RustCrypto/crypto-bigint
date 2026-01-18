//! Constant-time support: impls of `Ct*` traits and constant-time `const fn` operations.

use super::UintRef;
use crate::{Choice, CtAssign, CtEq};

impl CtAssign for UintRef {
    #[inline]
    fn ct_assign(&mut self, other: &Self, choice: Choice) {
        debug_assert_eq!(self.bits_precision(), other.bits_precision());
        self.as_mut_words().ct_assign(other.as_words(), choice);
    }
}

impl CtEq for UintRef {
    #[inline]
    fn ct_eq(&self, other: &Self) -> Choice {
        self.as_words().ct_eq(other.as_words())
    }
}
