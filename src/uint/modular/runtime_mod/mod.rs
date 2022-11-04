use crate::{Limb, UInt};

use super::{reduction::montgomery_reduction, GenericResidue};

/// Additions between residues with a modulus set at runtime
mod runtime_add;
/// Multiplications between residues with a modulus set at runtime
mod runtime_mul;
/// Exponentiation of residues with a modulus set at runtime
mod runtime_pow;

/// The parameters to efficiently go to and from the Montgomery form for a modulus provided at runtime.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ResidueParams<const LIMBS: usize> {
    // The constant modulus
    modulus: UInt<LIMBS>,
    // Parameter used in Montgomery reduction
    r: UInt<LIMBS>,
    // R^2, used to move into Montgomery form
    r2: UInt<LIMBS>,
    // The lowest limbs of -(MODULUS^-1) mod R
    // We only need the LSB because during reduction this value is multiplied modulo 2**64.
    mod_neg_inv: Limb,
}

/// A residue represented using `LIMBS` limbs. The modulus of this residue is set at runtime.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Residue<const LIMBS: usize> {
    montgomery_form: UInt<LIMBS>,
    residue_params: ResidueParams<LIMBS>,
}

impl<const LIMBS: usize> Residue<LIMBS> {
    /// Instantiates a new `Residue` that represents this `integer` mod `MOD`.
    pub const fn new(integer: UInt<LIMBS>, residue_params: ResidueParams<LIMBS>) -> Self {
        let mut modular_integer = Self {
            montgomery_form: integer,
            residue_params,
        };

        let product = integer.mul_wide(&residue_params.r2);
        modular_integer.montgomery_form =
            montgomery_reduction(product, residue_params.modulus, residue_params.mod_neg_inv);

        modular_integer
    }

    /// Retrieves the integer currently encoded in this `Residue`, guaranteed to be reduced.
    pub const fn retrieve(&self) -> UInt<LIMBS> {
        montgomery_reduction(
            (self.montgomery_form, UInt::ZERO),
            self.residue_params.modulus,
            self.residue_params.mod_neg_inv,
        )
    }
}

impl<const LIMBS: usize> GenericResidue<LIMBS> for Residue<LIMBS> {
    fn retrieve(&self) -> UInt<LIMBS> {
        self.retrieve()
    }
}
