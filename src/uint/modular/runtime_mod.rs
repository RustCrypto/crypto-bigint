use crate::{Limb, Uint, Word};

use super::{reduction::montgomery_reduction, Retrieve};

/// Additions between residues with a modulus set at runtime
mod runtime_add;
/// Multiplicative inverses of residues with a modulus set at runtime
mod runtime_inv;
/// Multiplications between residues with a modulus set at runtime
mod runtime_mul;
/// Negations of residues with a modulus set at runtime
mod runtime_neg;
/// Exponentiation of residues with a modulus set at runtime
mod runtime_pow;
/// Subtractions between residues with a modulus set at runtime
mod runtime_sub;

/// The parameters to efficiently go to and from the Montgomery form for a modulus provided at runtime.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct DynResidueParams<const LIMBS: usize> {
    // The constant modulus
    modulus: Uint<LIMBS>,
    // Parameter used in Montgomery reduction
    r: Uint<LIMBS>,
    // R^2, used to move into Montgomery form
    r2: Uint<LIMBS>,
    // R^3, used to compute the multiplicative inverse
    r3: Uint<LIMBS>,
    // The lowest limbs of -(MODULUS^-1) mod R
    // We only need the LSB because during reduction this value is multiplied modulo 2**Limb::BITS.
    mod_neg_inv: Limb,
}

impl<const LIMBS: usize> DynResidueParams<LIMBS> {
    /// Instantiates a new set of `ResidueParams` representing the given `modulus`.
    pub fn new(modulus: &Uint<LIMBS>) -> Self {
        let r = Uint::MAX.const_rem(modulus).0.wrapping_add(&Uint::ONE);
        let r2 = Uint::const_rem_wide(r.square_wide(), modulus).0;
        let mod_neg_inv =
            Limb(Word::MIN.wrapping_sub(modulus.inv_mod2k(Word::BITS as usize).limbs[0].0));
        let r3 = montgomery_reduction(&r2.square_wide(), modulus, mod_neg_inv);

        Self {
            modulus: *modulus,
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
    montgomery_form: Uint<LIMBS>,
    residue_params: DynResidueParams<LIMBS>,
}

impl<const LIMBS: usize> DynResidue<LIMBS> {
    /// Instantiates a new `Residue` that represents this `integer` mod `MOD`.
    pub const fn new(integer: &Uint<LIMBS>, residue_params: DynResidueParams<LIMBS>) -> Self {
        let product = integer.mul_wide(&residue_params.r2);
        let montgomery_form = montgomery_reduction(
            &product,
            &residue_params.modulus,
            residue_params.mod_neg_inv,
        );

        Self {
            montgomery_form,
            residue_params,
        }
    }

    /// Retrieves the integer currently encoded in this `Residue`, guaranteed to be reduced.
    pub const fn retrieve(&self) -> Uint<LIMBS> {
        montgomery_reduction(
            &(self.montgomery_form, Uint::ZERO),
            &self.residue_params.modulus,
            self.residue_params.mod_neg_inv,
        )
    }

    /// Instantiates a new `Residue` that represents zero.
    pub const fn zero(residue_params: DynResidueParams<LIMBS>) -> Self {
        Self {
            montgomery_form: Uint::<LIMBS>::ZERO,
            residue_params,
        }
    }

    /// Instantiates a new `Residue` that represents 1.
    pub const fn one(residue_params: DynResidueParams<LIMBS>) -> Self {
        Self {
            montgomery_form: residue_params.r,
            residue_params,
        }
    }
}

impl<const LIMBS: usize> Retrieve for DynResidue<LIMBS> {
    type Output = Uint<LIMBS>;
    fn retrieve(&self) -> Self::Output {
        self.retrieve()
    }
}
