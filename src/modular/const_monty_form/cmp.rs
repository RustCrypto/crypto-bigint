use super::{ConstMontyForm, ConstMontyParams};
use crate::{Choice, CtEq};

impl<MOD, const LIMBS: usize> CtEq for ConstMontyForm<MOD, LIMBS>
where
    MOD: ConstMontyParams<LIMBS>,
{
    fn ct_eq(&self, other: &Self) -> Choice {
        CtEq::ct_eq(&self.montgomery_form, &other.montgomery_form)
    }
}

#[cfg(feature = "subtle")]
impl<MOD, const LIMBS: usize> subtle::ConstantTimeEq for ConstMontyForm<MOD, LIMBS>
where
    MOD: ConstMontyParams<LIMBS>,
{
    fn ct_eq(&self, other: &Self) -> subtle::Choice {
        CtEq::ct_eq(&self.montgomery_form, &other.montgomery_form).into()
    }
}
