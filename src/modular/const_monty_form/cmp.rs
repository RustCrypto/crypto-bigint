use super::{ConstMontyForm, ConstMontyParams};
use crate::{ConstChoice, CtEq};

impl<MOD, const LIMBS: usize> CtEq for ConstMontyForm<MOD, LIMBS>
where
    MOD: ConstMontyParams<LIMBS>,
{
    fn ct_eq(&self, other: &Self) -> ConstChoice {
        CtEq::ct_eq(&self.montgomery_form, &other.montgomery_form)
    }
}

impl<MOD, const LIMBS: usize> subtle::ConstantTimeEq for ConstMontyForm<MOD, LIMBS>
where
    MOD: ConstMontyParams<LIMBS>,
{
    fn ct_eq(&self, other: &Self) -> subtle::Choice {
        CtEq::ct_eq(&self.montgomery_form, &other.montgomery_form).into()
    }
}
