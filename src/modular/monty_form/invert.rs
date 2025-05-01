//! Multiplicative inverses of integers in Montgomery form with a modulus set at runtime.

use super::{MontyForm, MontyParams};
use crate::{
    ConstCtOption, Inverter, Odd, PrecomputeInverter, PrecomputeInverterWithAdjuster, Uint,
    modular::SafeGcdInverter, traits::Invert,
};
use core::fmt;
use subtle::CtOption;

impl<const SAT_LIMBS: usize, const UNSAT_LIMBS: usize> MontyForm<SAT_LIMBS>
where
    Odd<Uint<SAT_LIMBS>>: PrecomputeInverter<
            Inverter = SafeGcdInverter<SAT_LIMBS, UNSAT_LIMBS>,
            Output = Uint<SAT_LIMBS>,
        >,
{
    /// Computes `self^-1` representing the multiplicative inverse of `self`.
    /// i.e. `self * self^-1 = 1`.
    ///
    /// If the number was invertible, the second element of the tuple is the truthy value,
    /// otherwise it is the falsy value (in which case the first element's value is unspecified).
    #[deprecated(since = "0.7.0", note = "please use `invert` instead")]
    pub const fn inv(&self) -> ConstCtOption<Self> {
        self.invert()
    }

    /// Computes `self^-1` representing the multiplicative inverse of `self`.
    /// i.e. `self * self^-1 = 1`.
    ///
    /// If the number was invertible, the second element of the tuple is the truthy value,
    /// otherwise it is the falsy value (in which case the first element's value is unspecified).
    pub const fn invert(&self) -> ConstCtOption<Self> {
        let inverter = self.params.inverter();
        let maybe_inverse = inverter.invert(&self.montgomery_form);
        let (inverse, inverse_is_some) = maybe_inverse.components_ref();

        let ret = Self {
            montgomery_form: *inverse,
            params: self.params,
        };

        ConstCtOption::new(ret, inverse_is_some)
    }

    /// Computes `self^-1` representing the multiplicative inverse of `self`.
    /// i.e. `self * self^-1 = 1`.
    ///
    /// If the number was invertible, the second element of the tuple is the truthy value,
    /// otherwise it is the falsy value (in which case the first element's value is unspecified).
    ///
    /// This version is variable-time with respect to the value of `self`, but constant-time with
    /// respect to `self`'s `params`.
    #[deprecated(since = "0.7.0", note = "please use `invert_vartime` instead")]
    pub const fn inv_vartime(&self) -> ConstCtOption<Self> {
        self.invert_vartime()
    }

    /// Computes `self^-1` representing the multiplicative inverse of `self`.
    /// i.e. `self * self^-1 = 1`.
    ///
    /// If the number was invertible, the second element of the tuple is the truthy value,
    /// otherwise it is the falsy value (in which case the first element's value is unspecified).
    ///
    /// This version is variable-time with respect to the value of `self`, but constant-time with
    /// respect to `self`'s `params`.
    pub const fn invert_vartime(&self) -> ConstCtOption<Self> {
        let inverter = self.params.inverter();
        let maybe_inverse = inverter.invert_vartime(&self.montgomery_form);
        let (inverse, inverse_is_some) = maybe_inverse.components_ref();

        let ret = Self {
            montgomery_form: *inverse,
            params: self.params,
        };

        ConstCtOption::new(ret, inverse_is_some)
    }
}

impl<const SAT_LIMBS: usize, const UNSAT_LIMBS: usize> Invert for MontyForm<SAT_LIMBS>
where
    Odd<Uint<SAT_LIMBS>>: PrecomputeInverter<
            Inverter = SafeGcdInverter<SAT_LIMBS, UNSAT_LIMBS>,
            Output = Uint<SAT_LIMBS>,
        >,
{
    type Output = CtOption<Self>;

    fn invert(&self) -> Self::Output {
        self.invert().into()
    }

    fn invert_vartime(&self) -> Self::Output {
        self.invert_vartime().into()
    }
}

impl<const SAT_LIMBS: usize, const UNSAT_LIMBS: usize> MontyParams<SAT_LIMBS>
where
    Odd<Uint<SAT_LIMBS>>: PrecomputeInverter<
            Inverter = SafeGcdInverter<SAT_LIMBS, UNSAT_LIMBS>,
            Output = Uint<SAT_LIMBS>,
        >,
{
    /// Create a modular inverter for the modulus of these params.
    // TODO(tarcieri): make `pub`?
    const fn inverter(&self) -> SafeGcdInverter<SAT_LIMBS, UNSAT_LIMBS> {
        SafeGcdInverter::new(&self.modulus, &self.r2)
    }
}

impl<const LIMBS: usize> PrecomputeInverter for MontyParams<LIMBS>
where
    Odd<Uint<LIMBS>>:
        PrecomputeInverter<Output = Uint<LIMBS>> + PrecomputeInverterWithAdjuster<Uint<LIMBS>>,
{
    type Inverter = MontyFormInverter<LIMBS>;
    type Output = MontyForm<LIMBS>;

    fn precompute_inverter(&self) -> MontyFormInverter<LIMBS> {
        MontyFormInverter {
            inverter: self.modulus.precompute_inverter_with_adjuster(&self.r2),
            params: *self,
        }
    }
}

/// Bernstein-Yang inverter which inverts [`MontyForm`] types.
pub struct MontyFormInverter<const LIMBS: usize>
where
    Odd<Uint<LIMBS>>: PrecomputeInverter<Output = Uint<LIMBS>>,
{
    inverter: <Odd<Uint<LIMBS>> as PrecomputeInverter>::Inverter,
    params: MontyParams<LIMBS>,
}

impl<const LIMBS: usize> Inverter for MontyFormInverter<LIMBS>
where
    Odd<Uint<LIMBS>>: PrecomputeInverter<Output = Uint<LIMBS>>,
{
    type Output = MontyForm<LIMBS>;

    fn invert(&self, value: &MontyForm<LIMBS>) -> CtOption<Self::Output> {
        debug_assert_eq!(self.params, value.params);

        self.inverter
            .invert(&value.montgomery_form)
            .map(|montgomery_form| MontyForm {
                montgomery_form,
                params: value.params,
            })
    }

    fn invert_vartime(&self, value: &MontyForm<LIMBS>) -> CtOption<Self::Output> {
        debug_assert_eq!(self.params, value.params);

        self.inverter
            .invert_vartime(&value.montgomery_form)
            .map(|montgomery_form| MontyForm {
                montgomery_form,
                params: value.params,
            })
    }
}

impl<const SAT_LIMBS: usize, const UNSAT_LIMBS: usize> fmt::Debug for MontyFormInverter<SAT_LIMBS>
where
    Odd<Uint<SAT_LIMBS>>: PrecomputeInverter<
            Inverter = SafeGcdInverter<SAT_LIMBS, UNSAT_LIMBS>,
            Output = Uint<SAT_LIMBS>,
        >,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("MontyFormInverter")
            .field("modulus", &self.inverter.modulus)
            .finish()
    }
}

#[cfg(test)]
mod tests {
    use super::{MontyForm, MontyParams};
    use crate::{Inverter, Odd, PrecomputeInverter, U256};

    fn params() -> MontyParams<{ U256::LIMBS }> {
        MontyParams::new_vartime(Odd::<U256>::from_be_hex(
            "15477BCCEFE197328255BFA79A1217899016D927EF460F4FF404029D24FA4409",
        ))
    }

    #[test]
    fn test_self_inverse() {
        let params = params();
        let x =
            U256::from_be_hex("77117F1273373C26C700D076B3F780074D03339F56DD0EFB60E7F58441FD3685");
        let x_monty = MontyForm::new(&x, params);

        let inv = x_monty.invert().unwrap();
        let res = x_monty * inv;

        assert_eq!(res.retrieve(), U256::ONE);
    }

    #[test]
    fn test_self_inverse_precomuted() {
        let params = params();
        let x =
            U256::from_be_hex("77117F1273373C26C700D076B3F780074D03339F56DD0EFB60E7F58441FD3685");
        let x_monty = MontyForm::new(&x, params);

        let inverter = params.precompute_inverter();
        let inv = inverter.invert(&x_monty).unwrap();
        let res = x_monty * inv;

        assert_eq!(res.retrieve(), U256::ONE);
    }
}
