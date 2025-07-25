//! Multiplicative inverses of integers in Montgomery form with a constant modulus.

use super::{ConstMontyForm, ConstMontyParams};
use crate::{
    ConstCtOption, Invert, Inverter, Odd, PrecomputeInverter, Uint, modular::SafeGcdInverter,
};
use core::{fmt, marker::PhantomData};
use subtle::CtOption;

impl<MOD: ConstMontyParams<LIMBS>, const LIMBS: usize> ConstMontyForm<MOD, LIMBS> {
    /// Computes `self^-1` representing the multiplicative inverse of `self`,
    /// i.e. `self * self^-1 = 1`.
    ///
    /// If the number was invertible, the second element of the tuple is the truthy value,
    /// otherwise it is the falsy value (in which case the first element's value is unspecified).
    #[deprecated(since = "0.7.0", note = "please use `invert` instead")]
    pub const fn inv(&self) -> ConstCtOption<Self> {
        self.invert()
    }

    /// Computes `self^-1` representing the multiplicative inverse of `self`,
    /// i.e. `self * self^-1 = 1`.
    ///
    /// If the number was invertible, the second element of the tuple is the truthy value,
    /// otherwise it is the falsy value (in which case the first element's value is unspecified).
    pub const fn invert(&self) -> ConstCtOption<Self> {
        let inverter = <Odd<Uint<LIMBS>> as PrecomputeInverter>::Inverter::new(
            &MOD::PARAMS.modulus,
            &MOD::PARAMS.r2,
        );

        let maybe_inverse = inverter.invert(&self.montgomery_form);
        let (inverse, inverse_is_some) = maybe_inverse.components_ref();

        let ret = Self {
            montgomery_form: *inverse,
            phantom: PhantomData,
        };

        ConstCtOption::new(ret, inverse_is_some)
    }

    /// Computes `self^-1` representing the multiplicative inverse of `self`,
    /// i.e. `self * self^-1 = 1`.
    ///
    /// If the number was invertible, the second element of the tuple is the truthy value,
    /// otherwise it is the falsy value (in which case the first element's value is unspecified).
    ///
    /// This version is variable-time with respect to the value of `self`, but constant-time with
    /// respect to `MOD`.
    #[deprecated(since = "0.7.0", note = "please use `invert_vartime` instead")]
    pub const fn inv_vartime(&self) -> ConstCtOption<Self> {
        self.invert_vartime()
    }

    /// Computes `self^-1` representing the multiplicative inverse of `self`,
    /// i.e. `self * self^-1 = 1`.
    ///
    /// If the number was invertible, the second element of the tuple is the truthy value,
    /// otherwise it is the falsy value (in which case the first element's value is unspecified).
    ///
    /// This version is variable-time with respect to the value of `self`, but constant-time with
    /// respect to `MOD`.
    pub const fn invert_vartime(&self) -> ConstCtOption<Self> {
        let inverter = <Odd<Uint<LIMBS>> as PrecomputeInverter>::Inverter::new(
            &MOD::PARAMS.modulus,
            &MOD::PARAMS.r2,
        );

        let maybe_inverse = inverter.invert_vartime(&self.montgomery_form);
        let (inverse, inverse_is_some) = maybe_inverse.components_ref();

        let ret = Self {
            montgomery_form: *inverse,
            phantom: PhantomData,
        };

        ConstCtOption::new(ret, inverse_is_some)
    }
}

impl<MOD: ConstMontyParams<LIMBS>, const LIMBS: usize> Invert for ConstMontyForm<MOD, LIMBS> {
    type Output = CtOption<Self>;

    fn invert(&self) -> Self::Output {
        self.invert().into()
    }

    fn invert_vartime(&self) -> Self::Output {
        self.invert_vartime().into()
    }
}

/// Bernstein-Yang inverter which inverts [`ConstMontyForm`] types.
pub struct ConstMontyFormInverter<MOD: ConstMontyParams<LIMBS>, const LIMBS: usize> {
    inverter: <Odd<Uint<LIMBS>> as PrecomputeInverter>::Inverter,
    phantom: PhantomData<MOD>,
}

impl<MOD: ConstMontyParams<LIMBS>, const LIMBS: usize> ConstMontyFormInverter<MOD, LIMBS> {
    /// Create a new [`ConstMontyFormInverter`] for the given [`ConstMontyParams`].
    #[allow(clippy::new_without_default)]
    pub const fn new() -> Self {
        let inverter = SafeGcdInverter::new(&MOD::PARAMS.modulus, &MOD::PARAMS.r2);

        Self {
            inverter,
            phantom: PhantomData,
        }
    }

    /// Returns either the adjusted modular multiplicative inverse for the argument or None
    /// depending on invertibility of the argument, i.e. its coprimality with the modulus.
    #[deprecated(since = "0.7.0", note = "please use `invert` instead")]
    pub const fn inv(
        &self,
        value: &ConstMontyForm<MOD, LIMBS>,
    ) -> ConstCtOption<ConstMontyForm<MOD, LIMBS>> {
        self.invert(value)
    }

    /// Returns either the adjusted modular multiplicative inverse for the argument or None
    /// depending on invertibility of the argument, i.e. its coprimality with the modulus.
    pub const fn invert(
        &self,
        value: &ConstMontyForm<MOD, LIMBS>,
    ) -> ConstCtOption<ConstMontyForm<MOD, LIMBS>> {
        let montgomery_form = self.inverter.invert(&value.montgomery_form);
        let (montgomery_form_ref, is_some) = montgomery_form.components_ref();
        let ret = ConstMontyForm {
            montgomery_form: *montgomery_form_ref,
            phantom: PhantomData,
        };
        ConstCtOption::new(ret, is_some)
    }

    /// Returns either the adjusted modular multiplicative inverse for the argument or None
    /// depending on invertibility of the argument, i.e. its coprimality with the modulus.
    ///
    /// This version is variable-time with respect to the value of `self`, but constant-time with
    /// respect to `MOD`.
    #[deprecated(since = "0.7.0", note = "please use `invert_vartime` instead")]
    pub const fn inv_vartime(
        &self,
        value: &ConstMontyForm<MOD, LIMBS>,
    ) -> ConstCtOption<ConstMontyForm<MOD, LIMBS>> {
        self.invert_vartime(value)
    }

    /// Returns either the adjusted modular multiplicative inverse for the argument or None
    /// depending on invertibility of the argument, i.e. its coprimality with the modulus.
    ///
    /// This version is variable-time with respect to the value of `self`, but constant-time with
    /// respect to `MOD`.
    pub const fn invert_vartime(
        &self,
        value: &ConstMontyForm<MOD, LIMBS>,
    ) -> ConstCtOption<ConstMontyForm<MOD, LIMBS>> {
        let montgomery_form = self.inverter.invert_vartime(&value.montgomery_form);
        let (montgomery_form_ref, is_some) = montgomery_form.components_ref();
        let ret = ConstMontyForm {
            montgomery_form: *montgomery_form_ref,
            phantom: PhantomData,
        };
        ConstCtOption::new(ret, is_some)
    }
}

impl<MOD: ConstMontyParams<LIMBS>, const LIMBS: usize> Inverter
    for ConstMontyFormInverter<MOD, LIMBS>
where
    Odd<Uint<LIMBS>>: PrecomputeInverter<Inverter = SafeGcdInverter<LIMBS>, Output = Uint<LIMBS>>,
{
    type Output = ConstMontyForm<MOD, LIMBS>;

    fn invert(&self, value: &ConstMontyForm<MOD, LIMBS>) -> CtOption<Self::Output> {
        self.invert(value).into()
    }

    fn invert_vartime(&self, value: &ConstMontyForm<MOD, LIMBS>) -> CtOption<Self::Output> {
        self.invert_vartime(value).into()
    }
}

impl<MOD: ConstMontyParams<LIMBS>, const LIMBS: usize> fmt::Debug
    for ConstMontyFormInverter<MOD, LIMBS>
where
    Odd<Uint<LIMBS>>: PrecomputeInverter<Inverter = SafeGcdInverter<LIMBS>, Output = Uint<LIMBS>>,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("ConstMontyFormInverter")
            .field("modulus", &self.inverter.modulus)
            .finish()
    }
}

#[cfg(test)]
mod tests {
    use super::ConstMontyParams;
    use crate::{U256, const_monty_form, const_monty_params};

    const_monty_params!(
        Modulus,
        U256,
        "15477BCCEFE197328255BFA79A1217899016D927EF460F4FF404029D24FA4409"
    );

    #[test]
    fn test_self_inverse() {
        let x =
            U256::from_be_hex("77117F1273373C26C700D076B3F780074D03339F56DD0EFB60E7F58441FD3685");
        let x_mod = const_monty_form!(x, Modulus);

        let inv = x_mod.invert().unwrap();
        let res = x_mod * inv;

        assert_eq!(res.retrieve(), U256::ONE);
    }

    #[test]
    fn test_self_inverse_precomputed() {
        let x =
            U256::from_be_hex("77117F1273373C26C700D076B3F780074D03339F56DD0EFB60E7F58441FD3685");
        let x_mod = const_monty_form!(x, Modulus);
        let inverter = Modulus::precompute_inverter();

        let inv = inverter.invert(&x_mod).unwrap();
        let res = x_mod * inv;

        assert_eq!(res.retrieve(), U256::ONE);
    }
}
