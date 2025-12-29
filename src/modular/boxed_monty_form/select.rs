use super::{BoxedMontyForm, BoxedMontyParams, BoxedMontyParamsInner};
use crate::{Choice, CtSelect};
use alloc::sync::Arc;

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
