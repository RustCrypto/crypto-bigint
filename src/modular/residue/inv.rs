//! Multiplicative inverses of residues with a constant modulus.

use super::{Residue, ResidueParams};
use crate::{
    modular::{inv::inv_montgomery_form, BernsteinYangInverter},
    ConstCtOption, Invert, Inverter, NonZero, PrecomputeInverter, Uint,
};
use core::{fmt, marker::PhantomData};
use subtle::CtOption;

impl<MOD: ResidueParams<LIMBS>, const LIMBS: usize> Residue<MOD, LIMBS> {
    /// Computes the residue `self^-1` representing the multiplicative inverse of `self`.
    /// I.e. `self * self^-1 = 1`.
    /// If the number was invertible, the second element of the tuple is the truthy value,
    /// otherwise it is the falsy value (in which case the first element's value is unspecified).
    pub const fn invert(&self) -> ConstCtOption<Self> {
        let maybe_inverse = inv_montgomery_form(
            &self.montgomery_form,
            &MOD::MODULUS.0,
            &MOD::R3,
            MOD::MOD_NEG_INV,
        );
        let (montgomery_form, is_some) = maybe_inverse.components_ref();

        let value = Self {
            montgomery_form: *montgomery_form,
            phantom: PhantomData,
        };

        ConstCtOption::new(value, is_some)
    }
}

impl<MOD: ResidueParams<LIMBS>, const LIMBS: usize> Invert for Residue<MOD, LIMBS> {
    type Output = CtOption<Self>;
    fn invert(&self) -> Self::Output {
        self.invert().into()
    }
}

impl<MOD: ResidueParams<LIMBS>, const LIMBS: usize> Invert for NonZero<Residue<MOD, LIMBS>> {
    type Output = Self;
    fn invert(&self) -> Self::Output {
        // Always succeeds for a non-zero argument
        let value = self.as_ref().invert().unwrap();
        // An inverse is necessarily non-zero
        NonZero::new(value).unwrap()
    }
}

/// Bernstein-Yang inverter which inverts [`Residue`] types.
pub struct ResidueInverter<MOD: ResidueParams<LIMBS>, const LIMBS: usize>
where
    Uint<LIMBS>: PrecomputeInverter<Output = Uint<LIMBS>>,
{
    inverter: <Uint<LIMBS> as PrecomputeInverter>::Inverter,
    phantom: PhantomData<MOD>,
}

impl<MOD: ResidueParams<SAT_LIMBS>, const SAT_LIMBS: usize, const UNSAT_LIMBS: usize>
    ResidueInverter<MOD, SAT_LIMBS>
where
    Uint<SAT_LIMBS>: PrecomputeInverter<
        Inverter = BernsteinYangInverter<SAT_LIMBS, UNSAT_LIMBS>,
        Output = Uint<SAT_LIMBS>,
    >,
{
    /// Create a new [`ResidueInverter`] for the given [`ResidueParams`].
    pub const fn new() -> Self {
        let inverter =
            BernsteinYangInverter::new(&MOD::MODULUS.0, &MOD::R2).expect("modulus should be valid");

        Self {
            inverter,
            phantom: PhantomData,
        }
    }

    /// Returns either the adjusted modular multiplicative inverse for the argument or None
    /// depending on invertibility of the argument, i.e. its coprimality with the modulus.
    pub const fn inv(
        &self,
        value: &Residue<MOD, SAT_LIMBS>,
    ) -> ConstCtOption<Residue<MOD, SAT_LIMBS>> {
        let montgomery_form = self.inverter.inv(&value.montgomery_form);
        let (montgomery_form_ref, is_some) = montgomery_form.components_ref();
        let ret = Residue {
            montgomery_form: *montgomery_form_ref,
            phantom: PhantomData,
        };
        ConstCtOption::new(ret, is_some)
    }
}

impl<MOD: ResidueParams<SAT_LIMBS>, const SAT_LIMBS: usize, const UNSAT_LIMBS: usize> Inverter
    for ResidueInverter<MOD, SAT_LIMBS>
where
    Uint<SAT_LIMBS>: PrecomputeInverter<
        Inverter = BernsteinYangInverter<SAT_LIMBS, UNSAT_LIMBS>,
        Output = Uint<SAT_LIMBS>,
    >,
{
    type Output = Residue<MOD, SAT_LIMBS>;

    fn invert(&self, value: &Residue<MOD, SAT_LIMBS>) -> CtOption<Self::Output> {
        self.inv(value).into()
    }
}

impl<MOD: ResidueParams<SAT_LIMBS>, const SAT_LIMBS: usize, const UNSAT_LIMBS: usize> fmt::Debug
    for ResidueInverter<MOD, SAT_LIMBS>
where
    Uint<SAT_LIMBS>: PrecomputeInverter<
        Inverter = BernsteinYangInverter<SAT_LIMBS, UNSAT_LIMBS>,
        Output = Uint<SAT_LIMBS>,
    >,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("ResidueInverter")
            .field("modulus", &self.inverter.modulus)
            .finish()
    }
}

#[cfg(test)]
mod tests {
    use super::ResidueParams;
    use crate::{const_residue, impl_modulus, Inverter, U256};

    impl_modulus!(
        Modulus,
        U256,
        "15477BCCEFE197328255BFA79A1217899016D927EF460F4FF404029D24FA4409"
    );

    #[test]
    fn test_self_inverse() {
        let x =
            U256::from_be_hex("77117F1273373C26C700D076B3F780074D03339F56DD0EFB60E7F58441FD3685");
        let x_mod = const_residue!(x, Modulus);

        let inv = x_mod.invert().unwrap();
        let res = x_mod * inv;

        assert_eq!(res.retrieve(), U256::ONE);
    }

    #[test]
    fn test_self_inverse_precomputed() {
        let x =
            U256::from_be_hex("77117F1273373C26C700D076B3F780074D03339F56DD0EFB60E7F58441FD3685");
        let x_mod = const_residue!(x, Modulus);
        let inverter = Modulus::precompute_inverter();

        let inv = inverter.invert(&x_mod).unwrap();
        let res = x_mod * inv;

        assert_eq!(res.retrieve(), U256::ONE);
    }
}
