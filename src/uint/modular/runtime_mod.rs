use crate::{Limb, UInt, Word};

use super::{reduction::montgomery_reduction, GenericResidue};

/// Additions between residues with a modulus set at runtime
mod runtime_add;
/// Multiplicative inverses of residues with a modulus set at runtime
mod runtime_inv;
/// Multiplications between residues with a modulus set at runtime
mod runtime_mul;
/// Exponentiation of residues with a modulus set at runtime
mod runtime_pow;

/// The parameters to efficiently go to and from the Montgomery form for a modulus provided at runtime.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct DynResidueParams<const LIMBS: usize> {
    // The constant modulus
    modulus: UInt<LIMBS>,
    // Parameter used in Montgomery reduction
    r: UInt<LIMBS>,
    // R^2, used to move into Montgomery form
    r2: UInt<LIMBS>,
    // R^3, used to compute the multiplicative inverse
    r3: UInt<LIMBS>,
    // The lowest limbs of -(MODULUS^-1) mod R
    // We only need the LSB because during reduction this value is multiplied modulo 2**64.
    mod_neg_inv: Limb,
}

impl<const LIMBS: usize> DynResidueParams<LIMBS> {
    /// Instantiates a new set of `ResidueParams` representing the given `modulus`.
    pub fn new(modulus: UInt<LIMBS>) -> Self {
        let r = UInt::MAX.ct_reduce(&modulus).0.wrapping_add(&UInt::ONE);
        let r2 = UInt::ct_reduce_wide(r.square_wide(), &modulus).0;
        let mod_neg_inv =
            Limb(Word::MIN.wrapping_sub(modulus.inv_mod2k(Word::BITS as usize).limbs[0].0));
        let r3 = montgomery_reduction(r2.square_wide(), modulus, mod_neg_inv);

        Self {
            modulus,
            r,
            r2,
            r3,
            mod_neg_inv,
        }
    }
}

/// A residue represented using `LIMBS` limbs. The odd modulus of this residue is set at runtime.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct DynResidue<const LIMBS: usize> {
    montgomery_form: UInt<LIMBS>,
    residue_params: DynResidueParams<LIMBS>,
}

impl<const LIMBS: usize> DynResidue<LIMBS> {
    /// Instantiates a new `Residue` that represents this `integer` mod `MOD`.
    pub const fn new(integer: UInt<LIMBS>, residue_params: DynResidueParams<LIMBS>) -> Self {
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

impl<const LIMBS: usize> GenericResidue<LIMBS> for DynResidue<LIMBS> {
    fn retrieve(&self) -> UInt<LIMBS> {
        self.retrieve()
    }
}
