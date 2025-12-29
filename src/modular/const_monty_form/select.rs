use super::{ConstMontyForm, ConstMontyParams};
use crate::{Choice, CtSelect, Uint};
use core::marker::PhantomData;

impl<MOD, const LIMBS: usize> CtSelect for ConstMontyForm<MOD, LIMBS>
where
    MOD: ConstMontyParams<LIMBS>,
{
    fn ct_select(&self, other: &Self, choice: Choice) -> Self {
        ConstMontyForm {
            montgomery_form: Uint::ct_select(&self.montgomery_form, &other.montgomery_form, choice),
            phantom: PhantomData,
        }
    }
}

#[cfg(feature = "subtle")]
impl<MOD, const LIMBS: usize> subtle::ConditionallySelectable for ConstMontyForm<MOD, LIMBS>
where
    MOD: ConstMontyParams<LIMBS> + Copy,
{
    fn conditional_select(a: &Self, b: &Self, choice: subtle::Choice) -> Self {
        CtSelect::ct_select(a, b, choice.into())
    }
}
