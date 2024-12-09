//! Multiplicative inverses of integers in Montgomery form with a constant modulus.

use super::{ConstMontyForm, ConstMontyParams};
use crate::{
    modular::SafeGcdInverter, ConstCtOption, Invert, Inverter, Odd, PrecomputeInverter, Uint,
};
use core::{fmt, marker::PhantomData};
use subtle::CtOption;

impl<MOD: ConstMontyParams<SAT_LIMBS>, const SAT_LIMBS: usize, const UNSAT_LIMBS: usize>
    ConstMontyForm<MOD, SAT_LIMBS>
where
    Odd<Uint<SAT_LIMBS>>: PrecomputeInverter<
        Inverter = SafeGcdInverter<SAT_LIMBS, UNSAT_LIMBS>,
        Output = Uint<SAT_LIMBS>,
    >,
{
    /// Computes `self^-1` representing the multiplicative inverse of `self`.
    /// I.e. `self * self^-1 = 1`.
    /// If the number was invertible, the second element of the tuple is the truthy value,
    /// otherwise it is the falsy value (in which case the first element's value is unspecified).
    pub const fn inv(&self) -> ConstCtOption<Self> {
        let inverter =
            <Odd<Uint<SAT_LIMBS>> as PrecomputeInverter>::Inverter::new(&MOD::MODULUS, &MOD::R2);

        let maybe_inverse = inverter.inv(&self.montgomery_form);
        let (inverse, inverse_is_some) = maybe_inverse.components_ref();

        let ret = Self {
            montgomery_form: *inverse,
            phantom: PhantomData,
        };

        ConstCtOption::new(ret, inverse_is_some)
    }
}

impl<MOD: ConstMontyParams<SAT_LIMBS>, const SAT_LIMBS: usize, const UNSAT_LIMBS: usize> Invert
    for ConstMontyForm<MOD, SAT_LIMBS>
where
    Odd<Uint<SAT_LIMBS>>: PrecomputeInverter<
        Inverter = SafeGcdInverter<SAT_LIMBS, UNSAT_LIMBS>,
        Output = Uint<SAT_LIMBS>,
    >,
{
    type Output = CtOption<Self>;
    fn invert(&self) -> Self::Output {
        self.inv().into()
    }
}

/// Bernstein-Yang inverter which inverts [`ConstMontyForm`] types.
pub struct ConstMontyFormInverter<MOD: ConstMontyParams<LIMBS>, const LIMBS: usize>
where
    Odd<Uint<LIMBS>>: PrecomputeInverter<Output = Uint<LIMBS>>,
{
    inverter: <Odd<Uint<LIMBS>> as PrecomputeInverter>::Inverter,
    phantom: PhantomData<MOD>,
}

impl<MOD: ConstMontyParams<SAT_LIMBS>, const SAT_LIMBS: usize, const UNSAT_LIMBS: usize>
    ConstMontyFormInverter<MOD, SAT_LIMBS>
where
    Odd<Uint<SAT_LIMBS>>: PrecomputeInverter<
        Inverter = SafeGcdInverter<SAT_LIMBS, UNSAT_LIMBS>,
        Output = Uint<SAT_LIMBS>,
    >,
{
    /// Create a new [`ConstMontyFormInverter`] for the given [`ConstMontyParams`].
    #[allow(clippy::new_without_default)]
    pub const fn new() -> Self {
        let inverter = SafeGcdInverter::new(&MOD::MODULUS, &MOD::R2);

        Self {
            inverter,
            phantom: PhantomData,
        }
    }

    /// Returns either the adjusted modular multiplicative inverse for the argument or None
    /// depending on invertibility of the argument, i.e. its coprimality with the modulus.
    pub const fn inv(
        &self,
        value: &ConstMontyForm<MOD, SAT_LIMBS>,
    ) -> ConstCtOption<ConstMontyForm<MOD, SAT_LIMBS>> {
        let montgomery_form = self.inverter.inv(&value.montgomery_form);
        let (montgomery_form_ref, is_some) = montgomery_form.components_ref();
        let ret = ConstMontyForm {
            montgomery_form: *montgomery_form_ref,
            phantom: PhantomData,
        };
        ConstCtOption::new(ret, is_some)
    }
}

impl<MOD: ConstMontyParams<SAT_LIMBS>, const SAT_LIMBS: usize, const UNSAT_LIMBS: usize> Inverter
    for ConstMontyFormInverter<MOD, SAT_LIMBS>
where
    Odd<Uint<SAT_LIMBS>>: PrecomputeInverter<
        Inverter = SafeGcdInverter<SAT_LIMBS, UNSAT_LIMBS>,
        Output = Uint<SAT_LIMBS>,
    >,
{
    type Output = ConstMontyForm<MOD, SAT_LIMBS>;

    fn invert(&self, value: &ConstMontyForm<MOD, SAT_LIMBS>) -> CtOption<Self::Output> {
        self.inv(value).into()
    }
}

impl<MOD: ConstMontyParams<SAT_LIMBS>, const SAT_LIMBS: usize, const UNSAT_LIMBS: usize> fmt::Debug
    for ConstMontyFormInverter<MOD, SAT_LIMBS>
where
    Odd<Uint<SAT_LIMBS>>: PrecomputeInverter<
        Inverter = SafeGcdInverter<SAT_LIMBS, UNSAT_LIMBS>,
        Output = Uint<SAT_LIMBS>,
    >,
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
    use crate::{const_monty_form, impl_modulus, Inverter, U256};

    impl_modulus!(
        Modulus,
        U256,
        "15477BCCEFE197328255BFA79A1217899016D927EF460F4FF404029D24FA4409"
    );

    #[test]
    fn test_self_inverse() {
        let x =
            U256::from_be_hex("77117F1273373C26C700D076B3F780074D03339F56DD0EFB60E7F58441FD3685");
        let x_mod = const_monty_form!(x, Modulus);

        let inv = x_mod.inv().unwrap();
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
