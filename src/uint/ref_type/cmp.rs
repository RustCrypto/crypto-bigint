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
        word::choice_from_lsb(self.limbs[0].0 & 1)
    }

    /// Returns [`Choice::TRUE`] if `self` != `0` or [`Choice::FALSE`] otherwise.
    #[inline]
    #[must_use]
    pub const fn is_nonzero(&self) -> Choice {
        let mut b = 0;
        let mut i = 0;
        while i < self.nlimbs() {
            b |= self.limbs[i].0;
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
            if self.limbs[i].0 != 0 {
                return false;
            }
            i += 1;
        }
        true
    }

    /// Returns the truthy value if `self < rhs` and the falsy value otherwise.
    ///
    /// # Panics
    /// If `lhs` and `rhs` are not the same size
    #[inline]
    pub(crate) const fn lt(lhs: &Self, rhs: &Self) -> Choice {
        // TODO(tarcieri): support for differently sized inputs?
        debug_assert!(
            lhs.bits_precision() == rhs.bits_precision(),
            "lhs and rhs sizes differ"
        );

        // NOTE: this is effectively a `borrowing_sub` that only computes the borrow
        let mut i = 0;
        let mut borrow = Limb::ZERO;

        while i < lhs.nlimbs() {
            borrow = lhs.limbs[i].borrowing_sub(rhs.limbs[i], borrow).1;
            i += 1;
        }

        borrow.lsb_to_choice()
    }
}

#[cfg(test)]
mod tests {
    use super::UintRef;
    use crate::Limb;

    #[test]
    fn lt() {
        let lesser = UintRef::new(&[Limb::ZERO, Limb::ZERO, Limb::ZERO]);
        let greater = UintRef::new(&[Limb::ZERO, Limb::ONE, Limb::ZERO]);
        assert!(UintRef::lt(lesser, greater).to_bool());
    }
}
