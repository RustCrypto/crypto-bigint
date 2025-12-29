use super::MontyParams;
use crate::modular::MontyForm;
use crate::{Choice, CtSelect, Odd, U64, Uint};

impl<const LIMBS: usize> CtSelect for MontyForm<LIMBS> {
    fn ct_select(&self, other: &Self, choice: Choice) -> Self {
        Self {
            montgomery_form: Uint::ct_select(&self.montgomery_form, &other.montgomery_form, choice),
            params: MontyParams::ct_select(&self.params, &other.params, choice),
        }
    }
}

impl<const LIMBS: usize> CtSelect for MontyParams<LIMBS> {
    fn ct_select(&self, other: &Self, choice: Choice) -> Self {
        Self {
            modulus: Odd::ct_select(&self.modulus, &other.modulus, choice),
            one: Uint::ct_select(&self.one, &other.one, choice),
            r2: Uint::ct_select(&self.r2, &other.r2, choice),
            mod_inv: U64::ct_select(&self.mod_inv, &other.mod_inv, choice),
            mod_leading_zeros: u32::ct_select(
                &self.mod_leading_zeros,
                &other.mod_leading_zeros,
                choice,
            ),
        }
    }
}

#[cfg(feature = "subtle")]
impl<const LIMBS: usize> subtle::ConditionallySelectable for MontyForm<LIMBS> {
    fn conditional_select(a: &Self, b: &Self, choice: subtle::Choice) -> Self {
        a.ct_select(b, choice.into())
    }
}

#[cfg(feature = "subtle")]
impl<const LIMBS: usize> subtle::ConditionallySelectable for MontyParams<LIMBS> {
    fn conditional_select(a: &Self, b: &Self, choice: subtle::Choice) -> Self {
        a.ct_select(b, choice.into())
    }
}
