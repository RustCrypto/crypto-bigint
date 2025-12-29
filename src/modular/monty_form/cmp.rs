use super::MontyParams;
use crate::modular::MontyForm;
use crate::{ConstChoice, CtEq};

impl<const LIMBS: usize> CtEq for MontyForm<LIMBS> {
    fn ct_eq(&self, other: &Self) -> ConstChoice {
        self.montgomery_form.ct_eq(&other.montgomery_form) & self.params.ct_eq(&other.params)
    }
}

impl<const LIMBS: usize> CtEq for MontyParams<LIMBS> {
    fn ct_eq(&self, other: &Self) -> ConstChoice {
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
