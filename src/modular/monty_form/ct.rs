//! Constant-time support: impls of `Ct*` traits and constant-time `const fn` operations.

use super::MontyParams;
use crate::{Choice, CtAssign, CtEq, modular::MontyForm};
use ctutils::{CtAssignSlice, CtEqSlice, CtSelectUsingCtAssign};

#[cfg(feature = "subtle")]
use crate::CtSelect;

impl<const LIMBS: usize> CtAssign for MontyForm<LIMBS> {
    fn ct_assign(&mut self, other: &Self, choice: Choice) {
        self.montgomery_form
            .ct_assign(&other.montgomery_form, choice);
        self.params.ct_assign(&other.params, choice);
    }
}
impl<const LIMBS: usize> CtAssignSlice for MontyForm<LIMBS> {}
impl<const LIMBS: usize> CtSelectUsingCtAssign for MontyForm<LIMBS> {}

impl<const LIMBS: usize> CtEq for MontyForm<LIMBS> {
    fn ct_eq(&self, other: &Self) -> Choice {
        self.montgomery_form.ct_eq(&other.montgomery_form) & self.params.ct_eq(&other.params)
    }
}
impl<const LIMBS: usize> CtEqSlice for MontyForm<LIMBS> {}

impl<const LIMBS: usize> CtAssign for MontyParams<LIMBS> {
    fn ct_assign(&mut self, other: &Self, choice: Choice) {
        self.modulus.ct_assign(&other.modulus, choice);
        self.one.ct_assign(&other.one, choice);
        self.r2.ct_assign(&other.r2, choice);
        self.mod_inv.ct_assign(&other.mod_inv, choice);
        self.mod_leading_zeros
            .ct_assign(&other.mod_leading_zeros, choice);
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

impl<const LIMBS: usize> CtSelectUsingCtAssign for MontyParams<LIMBS> {}

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
