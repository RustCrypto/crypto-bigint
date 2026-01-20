//! Modulus-specific Montgomery form parameters.

use crate::{Choice, CtAssign, CtEq, Limb, Odd, U64, Uint, Unsigned};
use core::fmt::{self, Debug};
use ctutils::{CtAssignSlice, CtEqSlice, CtSelectUsingCtAssign};

#[cfg(feature = "subtle")]
use crate::CtSelect;
#[cfg(feature = "zeroize")]
use zeroize::Zeroize;

/// Parameters to efficiently go to/from the Montgomery form for an odd modulus provided at runtime.
///
/// This version is generic over the underlying unsigned integer type.
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct GenericMontyParams<U: Unsigned> {
    /// The constant modulus.
    pub(super) modulus: Odd<U>,

    /// 1 in Montgomery form (a.k.a. `R`).
    pub(super) one: U,

    /// `R^2 mod modulus`, used to move into Montgomery form.
    pub(super) r2: U,

    /// The lowest limbs of `MODULUS^-1 mod 2**64`.
    ///
    /// This value is used in Montgomery reduction and modular inversion.
    pub(super) mod_inv: U64,

    /// Leading zeros in the modulus, used to choose optimized algorithms
    pub(super) mod_leading_zeros: u32,
}

/// Parameters to efficiently go to/from the Montgomery form for an odd modulus provided at runtime.
pub type MontyParams<const LIMBS: usize> = GenericMontyParams<Uint<LIMBS>>;

impl<U: Unsigned> GenericMontyParams<U> {
    /// Returns the modulus which was used to initialize these parameters.
    pub const fn modulus(&self) -> &Odd<U> {
        &self.modulus
    }

    /// 1 in Montgomery form (a.k.a. `R`).
    pub const fn one(&self) -> &U {
        &self.one
    }

    /// `R^2 mod modulus`, used to move into Montgomery form.
    pub const fn r2(&self) -> &U {
        &self.r2
    }

    /// Returns the modulus which was used to initialize these parameters.
    #[inline(always)]
    pub(crate) const fn mod_neg_inv(&self) -> Limb {
        self.mod_inv.limbs[0].wrapping_neg()
    }

    /// Core implementation of the debug impl which lets us customize it for various types/type
    /// aliases.
    pub(crate) fn debug_struct(&self, mut debug: fmt::DebugStruct<'_, '_>) -> fmt::Result {
        debug
            .field("modulus", &self.modulus)
            .field("one", &self.one)
            .field("r2", &self.r2)
            .field("mod_inv", &self.mod_inv)
            .field("mod_leading_zeros", &self.mod_leading_zeros)
            .finish()
    }
}

impl<U: Unsigned> AsRef<Self> for GenericMontyParams<U> {
    fn as_ref(&self) -> &Self {
        self
    }
}

impl<U: Unsigned> CtAssign for GenericMontyParams<U> {
    fn ct_assign(&mut self, other: &Self, choice: Choice) {
        self.modulus.ct_assign(&other.modulus, choice);
        self.one.ct_assign(&other.one, choice);
        self.r2.ct_assign(&other.r2, choice);
        self.mod_inv.ct_assign(&other.mod_inv, choice);
        self.mod_leading_zeros
            .ct_assign(&other.mod_leading_zeros, choice);
    }
}
impl<U: Unsigned> CtAssignSlice for GenericMontyParams<U> {}
impl<U: Unsigned> CtSelectUsingCtAssign for GenericMontyParams<U> {}

impl<U: Unsigned> CtEq for GenericMontyParams<U> {
    fn ct_eq(&self, other: &Self) -> Choice {
        self.modulus.ct_eq(&other.modulus)
            & self.one.ct_eq(&other.one)
            & self.r2.ct_eq(&other.r2)
            & self.mod_inv.ct_eq(&other.mod_inv)
    }
}
impl<U: Unsigned> CtEqSlice for GenericMontyParams<U> {}

impl<const LIMBS: usize> Debug for MontyParams<LIMBS> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.debug_struct(f.debug_struct("MontyParams"))
    }
}

#[cfg(feature = "subtle")]
impl<U: Unsigned> subtle::ConstantTimeEq for GenericMontyParams<U> {
    fn ct_eq(&self, other: &Self) -> subtle::Choice {
        CtEq::ct_eq(self, other).into()
    }
}

#[cfg(feature = "subtle")]
impl<U: Unsigned + Copy> subtle::ConditionallySelectable for GenericMontyParams<U> {
    fn conditional_assign(&mut self, src: &Self, choice: subtle::Choice) {
        self.ct_assign(src, choice.into());
    }

    fn conditional_select(a: &Self, b: &Self, choice: subtle::Choice) -> Self {
        a.ct_select(b, choice.into())
    }
}

#[cfg(feature = "zeroize")]
impl<U: Unsigned + Zeroize> Zeroize for GenericMontyParams<U> {
    fn zeroize(&mut self) {
        self.modulus.zeroize();
        self.one.zeroize();
        self.r2.zeroize();
        self.mod_inv.zeroize();
        self.mod_leading_zeros.zeroize();
    }
}
