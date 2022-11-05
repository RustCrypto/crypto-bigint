use crate::UInt;

use self::{add::AddResidue, inv::InvResidue, mul::MulResidue, pow::PowResidue};

mod reduction;

/// Implements `ConstResidue`s, supporting modular arithmetic with a constant modulus.
pub mod constant_mod;

mod add;
mod inv;
mod mul;
mod pow;

/// The `GenericResidue` trait provides a consistent API for dealing with residues with a constant modulus.
pub trait GenericResidue<const LIMBS: usize>:
    AddResidue + MulResidue + PowResidue<LIMBS> + InvResidue
{
    /// Retrieves the integer currently encoded in this `Residue`, guaranteed to be reduced.
    fn retrieve(&self) -> UInt<LIMBS>;
}

#[cfg(test)]
mod tests {
    use crate::{
        const_residue, impl_modulus,
        modular::{
            constant_mod::ConstResidue, constant_mod::ConstResidueParams,
            reduction::montgomery_reduction,
        },
        traits::Encoding,
        UInt, U256, U64,
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
                (Modulus2::R, UInt::ZERO),
                Modulus2::MODULUS,
                Modulus2::MOD_NEG_INV
            ),
            UInt::ONE
        );
    }

    #[test]
    fn test_reducing_r2() {
        // Divide the value R^2 by R, which should equal R
        assert_eq!(
            montgomery_reduction::<{ Modulus2::LIMBS }>(
                (Modulus2::R2, UInt::ZERO),
                Modulus2::MODULUS,
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
                (lo, hi),
                Modulus2::MODULUS,
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
        let product = x.mul_wide(&Modulus2::R);
        assert_eq!(
            montgomery_reduction::<{ Modulus2::LIMBS }>(
                product,
                Modulus2::MODULUS,
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
        let product = x.mul_wide(&Modulus2::R2);

        // Computing xR mod modulus without Montgomery reduction
        let (lo, hi) = x.mul_wide(&Modulus2::R);
        let c = hi.concat(&lo);
        let red = c.reduce(&U256::ZERO.concat(&Modulus2::MODULUS)).unwrap();
        let (hi, lo) = red.split();
        assert_eq!(hi, UInt::ZERO);

        assert_eq!(
            montgomery_reduction::<{ Modulus2::LIMBS }>(
                product,
                Modulus2::MODULUS,
                Modulus2::MOD_NEG_INV
            ),
            lo
        );
    }

    #[test]
    fn test_new_retrieve() {
        let x =
            U256::from_be_hex("44acf6b7e36c1342c2c5897204fe09504e1e2efb1a900377dbc4e7a6a133ec56");
        let x_mod = ConstResidue::<Modulus2, { Modulus2::LIMBS }>::new(x);

        // Confirm that when creating a Modular and retrieving the value, that it equals the original
        assert_eq!(x, x_mod.retrieve());
    }

    #[test]
    fn test_residue_macro() {
        let x =
            U256::from_be_hex("44acf6b7e36c1342c2c5897204fe09504e1e2efb1a900377dbc4e7a6a133ec56");
        assert_eq!(
            ConstResidue::<Modulus2, { Modulus2::LIMBS }>::new(x),
            const_residue!(x, Modulus2)
        );
    }
}
