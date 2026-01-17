//! Constant-time support: impls of `Ct*` traits.

use super::{BoxedMontyForm, BoxedMontyParams, BoxedMontyParamsInner};
use crate::{Choice, CtEq, CtSelect};
use alloc::sync::Arc;

impl CtEq for BoxedMontyForm {
    fn ct_eq(&self, other: &Self) -> Choice {
        self.montgomery_form.ct_eq(&other.montgomery_form) & self.params.ct_eq(&other.params)
    }
}

impl CtEq for BoxedMontyParams {
    fn ct_eq(&self, other: &Self) -> Choice {
        self.modulus().ct_eq(other.modulus())
            & self.one().ct_eq(other.one())
            & self.r2().ct_eq(other.r2())
            & self.mod_inv().ct_eq(&other.mod_inv())
    }
}

impl CtSelect for BoxedMontyForm {
    fn ct_select(&self, other: &Self, choice: Choice) -> Self {
        Self {
            montgomery_form: self
                .montgomery_form
                .ct_select(&other.montgomery_form, choice),
            params: self.params.ct_select(&other.params, choice),
        }
    }
}

impl CtSelect for BoxedMontyParams {
    fn ct_select(&self, other: &Self, choice: Choice) -> Self {
        Self(Arc::new(self.0.ct_select(&other.0, choice)))
    }
}

impl CtSelect for BoxedMontyParamsInner {
    fn ct_select(&self, other: &Self, choice: Choice) -> Self {
        Self {
            modulus: self.modulus.ct_select(&other.modulus, choice),
            one: self.one.ct_select(&other.one, choice),
            r2: self.r2.ct_select(&other.r2, choice),
            mod_inv: self.mod_inv.ct_select(&other.mod_inv, choice),
            mod_leading_zeros: self
                .mod_leading_zeros
                .ct_select(&other.mod_leading_zeros, choice),
        }
    }
}
