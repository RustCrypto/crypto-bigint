//! Constant-time support: impls of `Ct*` traits and constant-time `const fn` operations.

use super::UintRef;
use crate::{Choice, CtEq};

impl CtEq for UintRef {
    #[inline]
    fn ct_eq(&self, other: &Self) -> Choice {
        self.as_words().ct_eq(other.as_words())
    }
}
