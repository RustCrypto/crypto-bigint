//! Multiplicative inverses of residues with a modulus set at runtime.

use super::{DynResidue, DynResidueParams};
use crate::{
    modular::BernsteinYangInverter, traits::Invert, ConstCtOption, Inverter, PrecomputeInverter,
    PrecomputeInverterWithAdjuster, Uint,
};
use core::fmt;
use subtle::CtOption;

impl<const SAT_LIMBS: usize, const UNSAT_LIMBS: usize> DynResidue<SAT_LIMBS>
where
    Uint<SAT_LIMBS>: PrecomputeInverter<
        Inverter = BernsteinYangInverter<SAT_LIMBS, UNSAT_LIMBS>,
        Output = Uint<SAT_LIMBS>,
    >,
{
    /// Computes the residue `self^-1` representing the multiplicative inverse of `self`.
    /// I.e. `self * self^-1 = 1`.
    /// If the number was invertible, the second element of the tuple is the truthy value,
    /// otherwise it is the falsy value (in which case the first element's value is unspecified).
    pub const fn inv(&self) -> ConstCtOption<Self> {
        let maybe_inverter = <Uint<SAT_LIMBS> as PrecomputeInverter>::Inverter::new(
            &self.residue_params.modulus,
            &self.residue_params.r2,
        );
        let (inverter, inverter_is_some) = maybe_inverter.components_ref();

        let maybe_inverse = inverter.inv(&self.montgomery_form);
        let (inverse, inverse_is_some) = maybe_inverse.components_ref();

        let ret = Self {
            montgomery_form: *inverse,
            residue_params: self.residue_params,
        };

        ConstCtOption::new(ret, inverter_is_some.and(inverse_is_some))
    }
}

impl<const SAT_LIMBS: usize, const UNSAT_LIMBS: usize> Invert for DynResidue<SAT_LIMBS>
where
    Uint<SAT_LIMBS>: PrecomputeInverter<
        Inverter = BernsteinYangInverter<SAT_LIMBS, UNSAT_LIMBS>,
        Output = Uint<SAT_LIMBS>,
    >,
{
    type Output = CtOption<Self>;

    fn invert(&self) -> Self::Output {
        self.inv().into()
    }
}

impl<const LIMBS: usize> PrecomputeInverter for DynResidueParams<LIMBS>
where
    Uint<LIMBS>: PrecomputeInverter<Output = Uint<LIMBS>> + PrecomputeInverterWithAdjuster,
{
    type Inverter = DynResidueInverter<LIMBS>;
    type Output = DynResidue<LIMBS>;

    fn precompute_inverter(&self) -> DynResidueInverter<LIMBS> {
        DynResidueInverter {
            inverter: self.modulus.precompute_inverter_with_adjuster(&self.r2),
            residue_params: *self,
        }
    }
}

/// Bernstein-Yang inverter which inverts [`DynResidue`] types.
pub struct DynResidueInverter<const LIMBS: usize>
where
    Uint<LIMBS>: PrecomputeInverter<Output = Uint<LIMBS>>,
{
    inverter: <Uint<LIMBS> as PrecomputeInverter>::Inverter,
    residue_params: DynResidueParams<LIMBS>,
}

impl<const LIMBS: usize> Inverter for DynResidueInverter<LIMBS>
where
    Uint<LIMBS>: PrecomputeInverter<Output = Uint<LIMBS>>,
{
    type Output = DynResidue<LIMBS>;

    fn invert(&self, value: &DynResidue<LIMBS>) -> CtOption<Self::Output> {
        debug_assert_eq!(self.residue_params, value.residue_params);

        self.inverter
            .invert(&value.montgomery_form)
            .map(|montgomery_form| DynResidue {
                montgomery_form,
                residue_params: value.residue_params,
            })
    }
}

impl<const SAT_LIMBS: usize, const UNSAT_LIMBS: usize> fmt::Debug for DynResidueInverter<SAT_LIMBS>
where
    Uint<SAT_LIMBS>: PrecomputeInverter<
        Inverter = BernsteinYangInverter<SAT_LIMBS, UNSAT_LIMBS>,
        Output = Uint<SAT_LIMBS>,
    >,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("DynResidueInverter")
            .field("modulus", &self.inverter.modulus)
            .finish()
    }
}

#[cfg(test)]
mod tests {
    use super::{DynResidue, DynResidueParams};
    use crate::{Invert, Inverter, PrecomputeInverter, U256};

    fn residue_params() -> DynResidueParams<{ U256::LIMBS }> {
        DynResidueParams::new(&U256::from_be_hex(
            "15477BCCEFE197328255BFA79A1217899016D927EF460F4FF404029D24FA4409",
        ))
        .unwrap()
    }

    #[test]
    fn test_self_inverse() {
        let params = residue_params();
        let x =
            U256::from_be_hex("77117F1273373C26C700D076B3F780074D03339F56DD0EFB60E7F58441FD3685");
        let x_mod = DynResidue::new(&x, params);

        let inv = x_mod.invert().unwrap();
        let res = x_mod * inv;

        assert_eq!(res.retrieve(), U256::ONE);
    }

    #[test]
    fn test_self_inverse_precomuted() {
        let params = residue_params();
        let x =
            U256::from_be_hex("77117F1273373C26C700D076B3F780074D03339F56DD0EFB60E7F58441FD3685");
        let x_mod = DynResidue::new(&x, params);

        let inverter = params.precompute_inverter();
        let inv = inverter.invert(&x_mod).unwrap();
        let res = x_mod * inv;

        assert_eq!(res.retrieve(), U256::ONE);
    }
}
