use super::{BoxedMontyForm, BoxedMontyParams};
use crate::{ConstChoice, CtEq};

impl CtEq for BoxedMontyForm {
    fn ct_eq(&self, other: &Self) -> ConstChoice {
        self.montgomery_form.ct_eq(&other.montgomery_form) & self.params.ct_eq(&other.params)
    }
}

impl CtEq for BoxedMontyParams {
    fn ct_eq(&self, other: &Self) -> ConstChoice {
        self.modulus().ct_eq(other.modulus())
            & self.one().ct_eq(other.one())
            & self.r2().ct_eq(other.r2())
            & self.mod_inv().ct_eq(&other.mod_inv())
    }
}
