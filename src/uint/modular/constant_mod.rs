use core::marker::PhantomData;

use subtle::{Choice, ConditionallySelectable, ConstantTimeEq};

use crate::{Limb, Uint, Zero};

use super::{reduction::montgomery_reduction, Retrieve};

/// Additions between residues with a constant modulus
mod const_add;
/// Multiplicative inverses of residues with a constant modulus
mod const_inv;
/// Multiplications between residues with a constant modulus
mod const_mul;
/// Negations of residues with a constant modulus
mod const_neg;
/// Exponentiation of residues with a constant modulus
mod const_pow;
/// Subtractions between residues with a constant modulus
mod const_sub;

/// Macros to remove the boilerplate code when dealing with constant moduli.
#[macro_use]
mod macros;

pub use macros::*;

/// The parameters to efficiently go to and from the Montgomery form for a given odd modulus. An easy way to generate these parameters is using the `impl_modulus!` macro. These parameters are constant, so they cannot be set at runtime.
///
/// Unfortunately, `LIMBS` must be generic for now until const generics are stabilized.
pub trait ResidueParams<const LIMBS: usize>: Copy {
    /// Number of limbs required to encode a residue
    const LIMBS: usize;

    /// The constant modulus
    const MODULUS: Uint<LIMBS>;
    /// Parameter used in Montgomery reduction
    const R: Uint<LIMBS>;
    /// R^2, used to move into Montgomery form
    const R2: Uint<LIMBS>;
    /// R^3, used to perform a multiplicative inverse
    const R3: Uint<LIMBS>;
    /// The lowest limbs of -(MODULUS^-1) mod R
    // We only need the LSB because during reduction this value is multiplied modulo 2**Limb::BITS.
    const MOD_NEG_INV: Limb;
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
/// A residue mod `MOD`, represented using `LIMBS` limbs. The modulus of this residue is constant, so it cannot be set at runtime.
pub struct Residue<MOD, const LIMBS: usize>
where
    MOD: ResidueParams<LIMBS>,
{
    montgomery_form: Uint<LIMBS>,
    phantom: PhantomData<MOD>,
}

impl<MOD: ResidueParams<LIMBS>, const LIMBS: usize> Residue<MOD, LIMBS> {
    /// The representation of 0 mod `MOD`.
    pub const ZERO: Self = Self {
        montgomery_form: Uint::<LIMBS>::ZERO,
        phantom: PhantomData,
    };

    /// The representation of 1 mod `MOD`.
    pub const ONE: Self = Self {
        montgomery_form: MOD::R,
        phantom: PhantomData,
    };

    /// Instantiates a new `Residue` that represents this `integer` mod `MOD`.
    pub const fn new(integer: Uint<LIMBS>) -> Self {
        let mut modular_integer = Residue {
            montgomery_form: integer,
            phantom: PhantomData,
        };

        let product = integer.mul_wide(&MOD::R2);
        modular_integer.montgomery_form =
            montgomery_reduction::<LIMBS>(product, MOD::MODULUS, MOD::MOD_NEG_INV);

        modular_integer
    }

    /// Retrieves the integer currently encoded in this `Residue`, guaranteed to be reduced.
    pub const fn retrieve(&self) -> Uint<LIMBS> {
        montgomery_reduction::<LIMBS>(
            (self.montgomery_form, Uint::ZERO),
            MOD::MODULUS,
            MOD::MOD_NEG_INV,
        )
    }
}

impl<MOD: ResidueParams<LIMBS> + Copy, const LIMBS: usize> ConditionallySelectable
    for Residue<MOD, LIMBS>
{
    fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
        Residue {
            montgomery_form: Uint::conditional_select(
                &a.montgomery_form,
                &b.montgomery_form,
                choice,
            ),
            phantom: PhantomData,
        }
    }
}

impl<MOD: ResidueParams<LIMBS>, const LIMBS: usize> ConstantTimeEq for Residue<MOD, LIMBS> {
    fn ct_eq(&self, other: &Self) -> Choice {
        ConstantTimeEq::ct_eq(&self.montgomery_form, &other.montgomery_form)
    }
}

impl<MOD: ResidueParams<LIMBS>, const LIMBS: usize> Default for Residue<MOD, LIMBS> {
    fn default() -> Self {
        Self::ZERO
    }
}

impl<MOD: ResidueParams<LIMBS>, const LIMBS: usize> Zero for Residue<MOD, LIMBS> {
    const ZERO: Self = Self::ZERO;
}

impl<MOD: ResidueParams<LIMBS>, const LIMBS: usize> Retrieve for Residue<MOD, LIMBS> {
    type Output = Uint<LIMBS>;
    fn retrieve(&self) -> Self::Output {
        self.retrieve()
    }
}
