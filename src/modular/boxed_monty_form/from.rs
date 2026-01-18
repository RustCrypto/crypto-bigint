//! `From`-like conversions for [`BoxedMontyForm`] and [`BoxedMontyParams`].

use super::{BoxedMontyForm, BoxedMontyParams, GenericMontyParams};
use crate::modular::{ConstMontyForm, ConstMontyParams, MontyForm, MontyParams};

impl<const LIMBS: usize, Params> From<ConstMontyForm<Params, LIMBS>> for BoxedMontyForm
where
    Params: ConstMontyParams<LIMBS>,
{
    fn from(input: ConstMontyForm<Params, LIMBS>) -> Self {
        Self::from(&input)
    }
}

impl<const LIMBS: usize, Params> From<&ConstMontyForm<Params, LIMBS>> for BoxedMontyForm
where
    Params: ConstMontyParams<LIMBS>,
{
    fn from(input: &ConstMontyForm<Params, LIMBS>) -> Self {
        BoxedMontyForm {
            montgomery_form: input.as_montgomery().into(),
            params: Params::PARAMS.into(),
        }
    }
}

impl<const LIMBS: usize> From<MontyForm<LIMBS>> for BoxedMontyForm {
    fn from(input: MontyForm<LIMBS>) -> Self {
        Self::from(&input)
    }
}

impl<const LIMBS: usize> From<&MontyForm<LIMBS>> for BoxedMontyForm {
    fn from(input: &MontyForm<LIMBS>) -> Self {
        BoxedMontyForm {
            montgomery_form: input.as_montgomery().into(),
            params: input.params().into(),
        }
    }
}

impl<const LIMBS: usize> From<&MontyParams<LIMBS>> for BoxedMontyParams {
    fn from(params: &MontyParams<LIMBS>) -> Self {
        Self(
            GenericMontyParams {
                modulus: params.modulus.into(),
                one: params.one.into(),
                r2: params.r2.into(),
                mod_inv: params.mod_inv,
                mod_leading_zeros: params.mod_leading_zeros,
            }
            .into(),
        )
    }
}

impl<const LIMBS: usize> From<MontyParams<LIMBS>> for BoxedMontyParams {
    fn from(params: MontyParams<LIMBS>) -> Self {
        BoxedMontyParams::from(&params)
    }
}
