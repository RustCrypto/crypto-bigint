use core::ops::{Add, AddAssign};

use crate::{
    modular::{add::add_montgomery_form, AddResidue},
    Uint,
};

use super::DynResidue;

impl<const LIMBS: usize> AddResidue for DynResidue<LIMBS> {
    fn add(&self, rhs: &Self) -> Self {
        debug_assert_eq!(self.residue_params, rhs.residue_params);
        Self {
            montgomery_form: add_montgomery_form(
                &self.montgomery_form,
                &rhs.montgomery_form,
                &self.residue_params.modulus,
            ),
            residue_params: self.residue_params,
        }
    }
}

impl<const LIMBS: usize> AddAssign for DynResidue<LIMBS> {
    fn add_assign(&mut self, rhs: Self) {
        self.montgomery_form = add_montgomery_form(
            &self.montgomery_form,
            &rhs.montgomery_form,
            &self.residue_params.modulus,
        );
    }
}

impl<const LIMBS: usize> AddAssign<Uint<LIMBS>> for DynResidue<LIMBS> {
    fn add_assign(&mut self, rhs: Uint<LIMBS>) {
        self.montgomery_form = add_montgomery_form(
            &self.montgomery_form,
            &DynResidue::new(rhs, self.residue_params).montgomery_form,
            &self.residue_params.modulus,
        );
    }
}

impl<const LIMBS: usize> Add for DynResidue<LIMBS> {
    type Output = DynResidue<LIMBS>;

    fn add(mut self, rhs: Self) -> Self::Output {
        self += rhs;
        self
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        modular::runtime_mod::{DynResidue, DynResidueParams},
        U256,
    };

    #[test]
    fn add_overflow() {
        let params = DynResidueParams::new(U256::from_be_hex(
            "ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551",
        ));

        let x =
            U256::from_be_hex("44acf6b7e36c1342c2c5897204fe09504e1e2efb1a900377dbc4e7a6a133ec56");
        let mut x_mod = DynResidue::new(x, params);

        let y =
            U256::from_be_hex("d5777c45019673125ad240f83094d4252d829516fac8601ed01979ec1ec1a251");

        x_mod += y;

        let expected =
            U256::from_be_hex("1a2472fde50286541d97ca6a3592dd75beb9c9646e40c511b82496cfc3926956");

        assert_eq!(expected, x_mod.retrieve());
    }
}
