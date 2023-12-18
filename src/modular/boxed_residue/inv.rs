//! Multiplicative inverses of boxed residue.

use super::{BoxedResidue, BoxedResidueParams};
use crate::{
    modular::{reduction::montgomery_reduction_boxed_mut, BoxedBernsteinYangInverter},
    Invert, Inverter, PrecomputeInverter, PrecomputeInverterWithAdjuster,
};
use core::fmt;
use subtle::CtOption;

#[cfg(feature = "std")]
use std::sync::Arc;

impl BoxedResidue {
    /// Computes the residue `self^-1` representing the multiplicative inverse of `self`.
    /// I.e. `self * self^-1 = 1`.
    pub fn invert(&self) -> CtOption<Self> {
        let (mut inverse, is_some) = self
            .montgomery_form
            .inv_odd_mod(&self.residue_params.modulus);

        let mut product = inverse.mul(&self.residue_params.r3);

        montgomery_reduction_boxed_mut(
            &mut product,
            &self.residue_params.modulus,
            self.residue_params.mod_neg_inv,
            &mut inverse,
        );

        let value = Self {
            montgomery_form: inverse,
            residue_params: self.residue_params.clone(),
        };

        CtOption::new(value, is_some)
    }
}

impl Invert for BoxedResidue {
    type Output = CtOption<Self>;
    fn invert(&self) -> Self::Output {
        self.invert()
    }
}

impl PrecomputeInverter for BoxedResidueParams {
    type Inverter = BoxedResidueInverter;
    type Output = BoxedResidue;

    fn precompute_inverter(&self) -> BoxedResidueInverter {
        BoxedResidueInverter {
            inverter: self.modulus.precompute_inverter_with_adjuster(&self.r2),
            residue_params: self.clone().into(),
        }
    }
}

/// Bernstein-Yang inverter which inverts [`DynResidue`] types.
pub struct BoxedResidueInverter {
    /// Precomputed Bernstein-Yang inverter.
    inverter: BoxedBernsteinYangInverter,

    /// Residue parameters.
    #[cfg(not(feature = "std"))]
    residue_params: BoxedResidueParams,

    /// Residue parameters.
    // Uses `Arc` when `std` is available.
    #[cfg(feature = "std")]
    residue_params: Arc<BoxedResidueParams>,
}

impl Inverter for BoxedResidueInverter {
    type Output = BoxedResidue;

    fn invert(&self, value: &BoxedResidue) -> CtOption<Self::Output> {
        debug_assert_eq!(self.residue_params, value.residue_params);

        let montgomery_form = self.inverter.invert(&value.montgomery_form);
        let is_some = montgomery_form.is_some();
        let montgomery_form2 = value.montgomery_form.clone();
        let ret = BoxedResidue {
            montgomery_form: Option::from(montgomery_form).unwrap_or(montgomery_form2),
            residue_params: value.residue_params.clone(),
        };

        CtOption::new(ret, is_some)
    }
}

impl fmt::Debug for BoxedResidueInverter {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("BoxedResidueInverter")
            .field("modulus", &self.inverter.modulus)
            .finish()
    }
}

#[cfg(test)]
mod tests {
    use super::{BoxedResidue, BoxedResidueParams};
    use crate::{BoxedUint, Inverter, PrecomputeInverter};
    use hex_literal::hex;

    fn residue_params() -> BoxedResidueParams {
        BoxedResidueParams::new(
            BoxedUint::from_be_slice(
                &hex!("15477BCCEFE197328255BFA79A1217899016D927EF460F4FF404029D24FA4409"),
                256,
            )
            .unwrap(),
        )
        .unwrap()
    }

    #[test]
    fn test_self_inverse() {
        let params = residue_params();
        let x = BoxedUint::from_be_slice(
            &hex!("77117F1273373C26C700D076B3F780074D03339F56DD0EFB60E7F58441FD3685"),
            256,
        )
        .unwrap();
        let x_mod = BoxedResidue::new(x, params);

        let inv = x_mod.invert().unwrap();
        let res = x_mod * inv;

        assert!(bool::from(res.retrieve().is_one()));
    }

    #[test]
    fn test_self_inverse_precomuted() {
        let params = residue_params();
        let inverter = params.precompute_inverter();

        let x = BoxedUint::from_be_slice(
            &hex!("77117F1273373C26C700D076B3F780074D03339F56DD0EFB60E7F58441FD3685"),
            256,
        )
        .unwrap();
        let x_mod = BoxedResidue::new(x, params);
        let inv = inverter.invert(&x_mod).unwrap();
        let res = x_mod * inv;

        assert!(bool::from(res.retrieve().is_one()));
    }
}
