use core::ops::AddAssign;

use crate::{
    modular::{add::add_montgomery_form, AddResidue},
    Uint,
};

use super::{Residue, ResidueParams};

impl<MOD: ResidueParams<LIMBS>, const LIMBS: usize> AddResidue for Residue<MOD, LIMBS> {
    fn add(&self, rhs: &Self) -> Self {
        self.add(rhs)
    }
}

impl<MOD: ResidueParams<LIMBS>, const LIMBS: usize> Residue<MOD, LIMBS> {
    /// Adds two residues together.
    pub const fn add(&self, rhs: &Self) -> Self {
        Residue {
            montgomery_form: add_montgomery_form(
                &self.montgomery_form,
                &rhs.montgomery_form,
                &MOD::MODULUS,
            ),
            phantom: core::marker::PhantomData,
        }
    }
}

impl<MOD: ResidueParams<LIMBS>, const LIMBS: usize> AddAssign<&Uint<LIMBS>>
    for Residue<MOD, LIMBS>
{
    fn add_assign(&mut self, rhs: &Uint<LIMBS>) {
        *self += &Residue::new(*rhs);
    }
}

impl<MOD: ResidueParams<LIMBS>, const LIMBS: usize> AddAssign<&Self> for Residue<MOD, LIMBS> {
    fn add_assign(&mut self, rhs: &Self) {
        *self = self.add(rhs);
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
    fn add_overflow() {
        let x =
            U256::from_be_hex("44acf6b7e36c1342c2c5897204fe09504e1e2efb1a900377dbc4e7a6a133ec56");
        let mut x_mod = const_residue!(x, Modulus);

        let y =
            U256::from_be_hex("d5777c45019673125ad240f83094d4252d829516fac8601ed01979ec1ec1a251");

        x_mod += &y;

        let expected =
            U256::from_be_hex("1a2472fde50286541d97ca6a3592dd75beb9c9646e40c511b82496cfc3926956");

        assert_eq!(expected, x_mod.retrieve());
    }
}
