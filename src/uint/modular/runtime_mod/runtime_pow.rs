use super::DynResidue;
#[cfg(feature = "alloc")]
use crate::modular::{pow::multi_exponentiate_montgomery_form, runtime_mod::DynResidueParams};
use crate::{modular::pow::pow_montgomery_form, PowBoundedExp, Uint};

impl<const LIMBS: usize> DynResidue<LIMBS> {
    /// Raises to the `exponent` power.
    pub const fn pow<const RHS_LIMBS: usize>(
        &self,
        exponent: &Uint<RHS_LIMBS>,
    ) -> DynResidue<LIMBS> {
        self.pow_bounded_exp(exponent, Uint::<RHS_LIMBS>::BITS)
    }

    /// Raises to the `exponent` power,
    /// with `exponent_bits` representing the number of (least significant) bits
    /// to take into account for the exponent.
    ///
    /// NOTE: `exponent_bits` may be leaked in the time pattern.
    pub const fn pow_bounded_exp<const RHS_LIMBS: usize>(
        &self,
        exponent: &Uint<RHS_LIMBS>,
        exponent_bits: usize,
    ) -> Self {
        Self {
            montgomery_form: pow_montgomery_form(
                &self.montgomery_form,
                exponent,
                exponent_bits,
                &self.residue_params.modulus,
                &self.residue_params.r,
                self.residue_params.mod_neg_inv,
            ),
            residue_params: self.residue_params,
        }
    }

    #[cfg(feature = "alloc")]
    pub fn multi_exponentiate(
        bases_and_exponents: alloc::vec::Vec<(Self, Uint<LIMBS>)>,
        residue_params: DynResidueParams<LIMBS>,
    ) -> DynResidue<LIMBS> {
        Self::multi_exponentiate_bounded_exp(
            bases_and_exponents,
            Uint::<LIMBS>::BITS,
            residue_params,
        )
    }

    #[cfg(feature = "alloc")]
    pub fn multi_exponentiate_bounded_exp(
        bases_and_exponents: alloc::vec::Vec<(Self, Uint<LIMBS>)>,
        exponent_bits: usize,
        residue_params: DynResidueParams<LIMBS>,
    ) -> Self {
        let bases_and_exponents: alloc::vec::Vec<(Uint<LIMBS>, Uint<LIMBS>)> = bases_and_exponents
            .iter()
            .map(|(base, exp)| (base.montgomery_form, *exp))
            .collect();
        Self {
            montgomery_form: multi_exponentiate_montgomery_form(
                &bases_and_exponents,
                exponent_bits,
                &residue_params.modulus,
                &residue_params.r,
                residue_params.mod_neg_inv,
            ),
            residue_params,
        }
    }
}

impl<const LIMBS: usize> PowBoundedExp<Uint<LIMBS>> for DynResidue<LIMBS> {
    fn pow_bounded_exp(&self, exponent: &Uint<LIMBS>, exponent_bits: usize) -> Self {
        self.pow_bounded_exp(exponent, exponent_bits)
    }
}
