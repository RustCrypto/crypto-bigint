use core::marker::PhantomData;

use subtle::{Choice, ConditionallySelectable};

use crate::{Limb, UInt};

use super::{reduction::montgomery_reduction, GenericResidue};

/// Additions between residues with a constant modulus
mod const_add;
/// Multiplicative inverses of residues with a constant modulus
mod const_inv;
/// Multiplications between residues with a constant modulus
mod const_mul;
/// Exponentiation of residues with a constant modulus
mod const_pow;

#[macro_use]
/// Macros to remove the boilerplate code when dealing with constant moduli.
pub mod macros;

/// The parameters to efficiently go to and from the Montgomery form for a given odd modulus. An easy way to generate these parameters is using the `impl_modulus!` macro. These parameters are constant, so they cannot be set at runtime.
///
/// Unfortunately, `LIMBS` must be generic for now until const generics are stabilized.
pub trait ConstResidueParams<const LIMBS: usize>: Copy {
    /// Number of limbs required to encode a residue
    const LIMBS: usize;

    /// The constant modulus
    const MODULUS: UInt<LIMBS>;
    /// Parameter used in Montgomery reduction
    const R: UInt<LIMBS>;
    /// R^2, used to move into Montgomery form
    const R2: UInt<LIMBS>;
    /// R^3, used to perform a multiplicative inverse
    const R3: UInt<LIMBS>;
    /// The lowest limbs of -(MODULUS^-1) mod R
    // We only need the LSB because during reduction this value is multiplied modulo 2**64.
    const MOD_NEG_INV: Limb;
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
/// A residue mod `MOD`, represented using `LIMBS` limbs. The modulus of this residue is constant, so it cannot be set at runtime.
pub struct ConstResidue<MOD, const LIMBS: usize>
where
    MOD: ConstResidueParams<LIMBS>,
{
    montgomery_form: UInt<LIMBS>,
    phantom: PhantomData<MOD>,
}

impl<MOD: ConstResidueParams<LIMBS>, const LIMBS: usize> ConstResidue<MOD, LIMBS> {
    /// The representation of 1 mod `MOD`.
    pub const ONE: Self = Self {
        montgomery_form: MOD::R,
        phantom: PhantomData,
    };

    /// Instantiates a new `Residue` that represents this `integer` mod `MOD`.
    pub const fn new(integer: UInt<LIMBS>) -> Self {
        let mut modular_integer = ConstResidue {
            montgomery_form: integer,
            phantom: PhantomData,
        };

        let product = integer.mul_wide(&MOD::R2);
        modular_integer.montgomery_form =
            montgomery_reduction::<LIMBS>(product, MOD::MODULUS, MOD::MOD_NEG_INV);

        modular_integer
    }

    /// Retrieves the integer currently encoded in this `Residue`, guaranteed to be reduced.
    pub const fn retrieve(&self) -> UInt<LIMBS> {
        montgomery_reduction::<LIMBS>(
            (self.montgomery_form, UInt::ZERO),
            MOD::MODULUS,
            MOD::MOD_NEG_INV,
        )
    }
}

impl<MOD: ConstResidueParams<LIMBS>, const LIMBS: usize> GenericResidue<LIMBS>
    for ConstResidue<MOD, LIMBS>
{
    fn retrieve(&self) -> UInt<LIMBS> {
        self.retrieve()
    }
}

impl<MOD: ConstResidueParams<LIMBS> + Copy, const LIMBS: usize> ConditionallySelectable
    for ConstResidue<MOD, LIMBS>
{
    fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
        ConstResidue {
            montgomery_form: UInt::conditional_select(
                &a.montgomery_form,
                &b.montgomery_form,
                choice,
            ),
            phantom: PhantomData,
        }
    }
}
