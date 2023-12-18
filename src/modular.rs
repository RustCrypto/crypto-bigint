//! Modular arithmetic support.
//!
//! This module provides support for various modular arithmetic operations, implemented in terms of
//! Montgomery form.
//!
//! # Constant moduli
//!
//! The [`Residue`] and [`ResidueParams`] types implement support for modular arithmetic where the
//! modulus is fixed at compile-time.
//!
//! The [`impl_modulus!`][`crate::impl_modulus`] macro can be used to define a compile-time modulus,
//! whereas the [`const_residue!`][`crate::const_residue`] macro can define a [`Residue`] constant.
//!
//! # Dynamic moduli chosen at runtime
//!
//! The [`DynResidue`] and [`DynResidueParams`] types implement support for modular arithmetic where
//! the modulus can vary at runtime.

mod dyn_residue;
mod reduction;
mod residue;

mod add;
mod bernstein_yang;
mod div_by_2;
mod inv;
mod mul;
mod pow;
mod sub;

#[cfg(feature = "alloc")]
pub(crate) mod boxed_residue;

pub use self::{
    bernstein_yang::BernsteinYangInverter,
    dyn_residue::{inv::DynResidueInverter, DynResidue, DynResidueParams},
    reduction::montgomery_reduction,
    residue::{inv::ResidueInverter, Residue, ResidueParams},
};

#[cfg(feature = "alloc")]
pub use self::{
    bernstein_yang::boxed::BoxedBernsteinYangInverter,
    boxed_residue::{BoxedResidue, BoxedResidueParams},
};

/// A generalization for numbers kept in optimized representations (e.g. Montgomery)
/// that can be converted back to the original form.
pub trait Retrieve {
    /// The original type.
    type Output;

    /// Convert the number back from the optimized representation.
    fn retrieve(&self) -> Self::Output;
}

#[cfg(test)]
mod tests {
    use crate::{
        const_residue, impl_modulus,
        modular::{
            reduction::montgomery_reduction,
            residue::{Residue, ResidueParams},
        },
        NonZero, Uint, U256, U64,
    };

    impl_modulus!(
        Modulus1,
        U256,
        "73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001"
    );

    #[test]
    fn test_montgomery_params() {
        assert_eq!(
            Modulus1::R,
            U256::from_be_hex("1824b159acc5056f998c4fefecbc4ff55884b7fa0003480200000001fffffffe")
        );
        assert_eq!(
            Modulus1::R2,
            U256::from_be_hex("0748d9d99f59ff1105d314967254398f2b6cedcb87925c23c999e990f3f29c6d")
        );
        assert_eq!(
            Modulus1::MOD_NEG_INV,
            U64::from_be_hex("fffffffeffffffff").limbs[0]
        );
    }

    impl_modulus!(
        Modulus2,
        U256,
        "ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551"
    );

    #[test]
    fn test_reducing_r() {
        // Divide the value R by R, which should equal 1
        assert_eq!(
            montgomery_reduction::<{ Modulus2::LIMBS }>(
                &(Modulus2::R, Uint::ZERO),
                &Modulus2::MODULUS,
                Modulus2::MOD_NEG_INV
            ),
            Uint::ONE
        );
    }

    #[test]
    fn test_reducing_r2() {
        // Divide the value R^2 by R, which should equal R
        assert_eq!(
            montgomery_reduction::<{ Modulus2::LIMBS }>(
                &(Modulus2::R2, Uint::ZERO),
                &Modulus2::MODULUS,
                Modulus2::MOD_NEG_INV
            ),
            Modulus2::R
        );
    }

    #[test]
    fn test_reducing_r2_wide() {
        // Divide the value R^2 by R, which should equal R
        let (hi, lo) = Modulus2::R.square().split();
        assert_eq!(
            montgomery_reduction::<{ Modulus2::LIMBS }>(
                &(lo, hi),
                &Modulus2::MODULUS,
                Modulus2::MOD_NEG_INV
            ),
            Modulus2::R
        );
    }

    #[test]
    fn test_reducing_xr_wide() {
        // Reducing xR should return x
        let x =
            U256::from_be_hex("44acf6b7e36c1342c2c5897204fe09504e1e2efb1a900377dbc4e7a6a133ec56");
        let product = x.split_mul(&Modulus2::R);
        assert_eq!(
            montgomery_reduction::<{ Modulus2::LIMBS }>(
                &product,
                &Modulus2::MODULUS,
                Modulus2::MOD_NEG_INV
            ),
            x
        );
    }

    #[test]
    fn test_reducing_xr2_wide() {
        // Reducing xR^2 should return xR
        let x =
            U256::from_be_hex("44acf6b7e36c1342c2c5897204fe09504e1e2efb1a900377dbc4e7a6a133ec56");
        let product = x.split_mul(&Modulus2::R2);

        // Computing xR mod modulus without Montgomery reduction
        let (lo, hi) = x.split_mul(&Modulus2::R);
        let c = hi.concat(&lo);
        let red = c.rem(&NonZero::new(U256::ZERO.concat(&Modulus2::MODULUS)).unwrap());
        let (hi, lo) = red.split();
        assert_eq!(hi, Uint::ZERO);

        assert_eq!(
            montgomery_reduction::<{ Modulus2::LIMBS }>(
                &product,
                &Modulus2::MODULUS,
                Modulus2::MOD_NEG_INV
            ),
            lo
        );
    }

    #[test]
    fn test_new_retrieve() {
        let x =
            U256::from_be_hex("44acf6b7e36c1342c2c5897204fe09504e1e2efb1a900377dbc4e7a6a133ec56");
        let x_mod = Residue::<Modulus2, { Modulus2::LIMBS }>::new(&x);

        // Confirm that when creating a Modular and retrieving the value, that it equals the original
        assert_eq!(x, x_mod.retrieve());
    }

    #[test]
    fn test_residue_macro() {
        let x =
            U256::from_be_hex("44acf6b7e36c1342c2c5897204fe09504e1e2efb1a900377dbc4e7a6a133ec56");
        assert_eq!(
            Residue::<Modulus2, { Modulus2::LIMBS }>::new(&x),
            const_residue!(x, Modulus2)
        );
    }
}
