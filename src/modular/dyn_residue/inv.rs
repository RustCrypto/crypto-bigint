//! Multiplicative inverses of residues with a modulus set at runtime.

use super::{DynResidue, DynResidueParams};
use crate::{
    modular::{inv::inv_montgomery_form, BernsteinYangInverter},
    traits::Invert,
    ConstChoice, Inverter, PrecomputeInverter, PrecomputeInverterWithAdjuster, Uint,
};
use core::fmt;
use subtle::CtOption;

impl<const LIMBS: usize> DynResidue<LIMBS> {
    /// Computes the residue `self^-1` representing the multiplicative inverse of `self`.
    /// I.e. `self * self^-1 = 1`.
    /// If the number was invertible, the second element of the tuple is the truthy value,
    /// otherwise it is the falsy value (in which case the first element's value is unspecified).
    pub const fn invert(&self) -> (Self, ConstChoice) {
        let (montgomery_form, is_some) = inv_montgomery_form(
            &self.montgomery_form,
            &self.residue_params.modulus,
            &self.residue_params.r3,
            self.residue_params.mod_neg_inv,
        );

        let value = Self {
            montgomery_form,
            residue_params: self.residue_params,
        };

        (value, is_some)
    }
}

impl<const LIMBS: usize> Invert for DynResidue<LIMBS> {
    type Output = CtOption<Self>;
    fn invert(&self) -> Self::Output {
        let (value, is_some) = self.invert();
        CtOption::new(value, is_some.into())
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
    use crate::{Inverter, PrecomputeInverter, U256};

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

        let (inv, _is_some) = x_mod.invert();
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
