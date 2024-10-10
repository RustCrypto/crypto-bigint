//! [`Int`] division operations.

use subtle::{Choice, ConstantTimeEq, CtOption};

use crate::{CheckedDiv, Uint};
use crate::int::Int;

impl<const LIMBS: usize> CheckedDiv for Int<LIMBS> {
    fn checked_div(&self, rhs: &Self) -> CtOption<Self> {
        self.magnitude.checked_div(&rhs.magnitude)
            .and_then(|magnitude| {
                let res_is_zero = magnitude.ct_eq(&Uint::ZERO);
                let is_negative = (self.is_negative() ^ rhs.is_negative()) & !res_is_zero;
                CtOption::new(Int::new_from_uint(is_negative.into(), magnitude), Choice::from(1u8))
            }
        )
    }
}
