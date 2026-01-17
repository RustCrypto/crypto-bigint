//! Constant-time support: impls of `Ct*` traits and constant-time `const fn` operations.

use super::MontyParams;
use crate::{Choice, CtEq, CtSelect, Odd, U64, Uint, modular::MontyForm};

impl<const LIMBS: usize> CtEq for MontyForm<LIMBS> {
    fn ct_eq(&self, other: &Self) -> Choice {
        self.montgomery_form.ct_eq(&other.montgomery_form) & self.params.ct_eq(&other.params)
    }
}

impl<const LIMBS: usize> CtEq for MontyParams<LIMBS> {
    fn ct_eq(&self, other: &Self) -> Choice {
        self.modulus.ct_eq(&other.modulus)
            & self.one.ct_eq(&other.one)
            & self.r2.ct_eq(&other.r2)
            & self.mod_inv.ct_eq(&other.mod_inv)
    }
}

#[cfg(feature = "subtle")]
impl<const LIMBS: usize> subtle::ConstantTimeEq for MontyForm<LIMBS> {
    fn ct_eq(&self, other: &Self) -> subtle::Choice {
        CtEq::ct_eq(self, other).into()
    }
}

#[cfg(feature = "subtle")]
impl<const LIMBS: usize> subtle::ConstantTimeEq for MontyParams<LIMBS> {
    fn ct_eq(&self, other: &Self) -> subtle::Choice {
        CtEq::ct_eq(self, other).into()
    }
}

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
