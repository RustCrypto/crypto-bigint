use core::ops::Neg;

use crate::modular::neg::neg_montgomery_form;

use super::{Residue, ResidueParams};

impl<MOD: ResidueParams<LIMBS>, const LIMBS: usize> Neg for Residue<MOD, LIMBS> {
    type Output = Self;

    fn neg(self) -> Self {
        Residue::neg(&self)
    }
}

impl<MOD: ResidueParams<LIMBS>, const LIMBS: usize> Residue<MOD, LIMBS> {
    /// Computes the (reduced) negative of a residue.
    pub const fn neg(&self) -> Self {
        Residue {
            montgomery_form: neg_montgomery_form(&self.montgomery_form, &MOD::MODULUS),
            phantom: core::marker::PhantomData,
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        const_residue, impl_modulus, modular::constant_mod::ResidueParams, traits::Encoding, U256,
    };

    impl_modulus!(
        Modulus,
        U256,
        "ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551"
    );

    #[test]
    fn neg() {
        let x =
            U256::from_be_hex("44acf6b7e36c1342c2c5897204fe09504e1e2efb1a900377dbc4e7a6a133ec56");
        let mut x_mod = const_residue!(x, Modulus);

        x_mod = -x_mod;

        let expected =
            U256::from_be_hex("bb5309471c93ecbe3d3a768dfb01f6af6ec8cbb28c879b0d17f4e31c5b2f38fb");

        assert_eq!(expected, x_mod.retrieve());
    }
}
