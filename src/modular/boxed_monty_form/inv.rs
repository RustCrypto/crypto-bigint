//! Multiplicative inverses of boxed integers in Montgomery form.

use super::{BoxedMontyForm, BoxedMontyParams};
use crate::{
    modular::BoxedSafeGcdInverter, Invert, Inverter, PrecomputeInverter,
    PrecomputeInverterWithAdjuster,
};
use alloc::sync::Arc;
use core::fmt;
use subtle::CtOption;

impl BoxedMontyForm {
    /// Computes `self^-1` representing the multiplicative inverse of `self`.
    /// I.e. `self * self^-1 = 1`.
    pub fn invert(&self) -> CtOption<Self> {
        let inverter = self.params.precompute_inverter();
        inverter.invert(self)
    }
}

impl Invert for BoxedMontyForm {
    type Output = CtOption<Self>;
    fn invert(&self) -> Self::Output {
        self.invert()
    }
}

impl PrecomputeInverter for BoxedMontyParams {
    type Inverter = BoxedMontyFormInverter;
    type Output = BoxedMontyForm;

    fn precompute_inverter(&self) -> BoxedMontyFormInverter {
        BoxedMontyFormInverter {
            inverter: self.modulus.precompute_inverter_with_adjuster(&self.r2),
            params: self.clone().into(),
        }
    }
}

/// Bernstein-Yang inverter which inverts [`DynResidue`] types.
pub struct BoxedMontyFormInverter {
    /// Precomputed Bernstein-Yang inverter.
    inverter: BoxedSafeGcdInverter,

    /// Residue parameters.
    params: Arc<BoxedMontyParams>,
}

impl Inverter for BoxedMontyFormInverter {
    type Output = BoxedMontyForm;

    fn invert(&self, value: &BoxedMontyForm) -> CtOption<Self::Output> {
        debug_assert_eq!(self.params, value.params);

        let montgomery_form = self.inverter.invert(&value.montgomery_form);
        let is_some = montgomery_form.is_some();
        let montgomery_form2 = value.montgomery_form.clone();
        let ret = BoxedMontyForm {
            montgomery_form: Option::from(montgomery_form).unwrap_or(montgomery_form2),
            params: value.params.clone(),
        };

        CtOption::new(ret, is_some)
    }
}

impl fmt::Debug for BoxedMontyFormInverter {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("BoxedMontyFormInverter")
            .field("modulus", &self.inverter.modulus)
            .finish()
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        modular::{BoxedMontyForm, BoxedMontyParams},
        BoxedUint,
    };
    use hex_literal::hex;

    fn monty_params() -> BoxedMontyParams {
        BoxedMontyParams::new(
            BoxedUint::from_be_slice(
                &hex!("15477BCCEFE197328255BFA79A1217899016D927EF460F4FF404029D24FA4409"),
                256,
            )
            .unwrap()
            .to_odd()
            .unwrap(),
        )
    }

    #[test]
    fn test_self_inverse() {
        let params = monty_params();
        let x = BoxedUint::from_be_slice(
            &hex!("77117F1273373C26C700D076B3F780074D03339F56DD0EFB60E7F58441FD3685"),
            256,
        )
        .unwrap();
        let x_mod = BoxedMontyForm::new(x, params);

        let inv = x_mod.invert().unwrap();
        let res = x_mod * inv;

        assert!(bool::from(res.retrieve().is_one()));
    }
}
