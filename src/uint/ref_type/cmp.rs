//! [`UintRef`] comparison operations.
//!
//! Constant time unless explicitly noted otherwise.

use super::UintRef;
use crate::{Limb, word};
use ctutils::Choice;

impl UintRef {
    /// Returns the truthy value if `self` is odd or the falsy value otherwise.
    #[inline]
    #[must_use]
    pub const fn is_odd(&self) -> Choice {
        debug_assert!(self.nlimbs() >= 1, "should have limbs");
        word::choice_from_lsb(self.0[0].0 & 1)
    }

    /// Returns [`Choice::TRUE`] if `self` != `0` or [`Choice::FALSE`] otherwise.
    #[inline]
    #[must_use]
    pub const fn is_nonzero(&self) -> Choice {
        let mut b = 0;
        let mut i = 0;
        while i < self.nlimbs() {
            b |= self.0[i].0;
            i += 1;
        }
        Limb(b).is_nonzero()
    }

    /// Are all of limbs equal to `0`?
    #[inline]
    #[must_use]
    pub const fn is_zero(&self) -> Choice {
        self.is_nonzero().not()
    }

    /// Determine in variable time whether the `self` is zero.
    #[inline]
    pub(crate) const fn is_zero_vartime(&self) -> bool {
        let mut i = 0;
        while i < self.nlimbs() {
            if self.0[i].0 != 0 {
                return false;
            }
            i += 1;
        }
        true
    }
}
