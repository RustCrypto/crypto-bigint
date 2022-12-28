use core::ops::{Sub, SubAssign};

use crate::{
    modular::{sub::sub_montgomery_form, SubResidue},
    Uint,
};

use super::DynResidue;

impl<const LIMBS: usize> SubResidue for DynResidue<LIMBS> {
    fn sub(&self, rhs: &Self) -> Self {
        debug_assert_eq!(self.residue_params, rhs.residue_params);
        Self {
            montgomery_form: sub_montgomery_form(
                &self.montgomery_form,
                &rhs.montgomery_form,
                &self.residue_params.modulus,
            ),
            residue_params: self.residue_params,
        }
    }
}

impl<const LIMBS: usize> SubAssign for DynResidue<LIMBS> {
    fn sub_assign(&mut self, rhs: Self) {
        self.montgomery_form = sub_montgomery_form(
            &self.montgomery_form,
            &rhs.montgomery_form,
            &self.residue_params.modulus,
        );
    }
}

impl<const LIMBS: usize> SubAssign<Uint<LIMBS>> for DynResidue<LIMBS> {
    fn sub_assign(&mut self, rhs: Uint<LIMBS>) {
        self.montgomery_form = sub_montgomery_form(
            &self.montgomery_form,
            &DynResidue::new(rhs, self.residue_params).montgomery_form,
            &self.residue_params.modulus,
        );
    }
}

impl<const LIMBS: usize> Sub for DynResidue<LIMBS> {
    type Output = DynResidue<LIMBS>;

    fn sub(mut self, rhs: Self) -> Self::Output {
        self -= rhs;
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
    fn sub_overflow() {
        let params = DynResidueParams::new(U256::from_be_hex(
            "ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551",
        ));

        let x =
            U256::from_be_hex("44acf6b7e36c1342c2c5897204fe09504e1e2efb1a900377dbc4e7a6a133ec56");
        let mut x_mod = DynResidue::new(x, params);

        let y =
            U256::from_be_hex("d5777c45019673125ad240f83094d4252d829516fac8601ed01979ec1ec1a251");

        x_mod -= y;

        let expected =
            U256::from_be_hex("6f357a71e1d5a03167f34879d469352add829491c6df41ddff65387d7ed56f56");

        assert_eq!(expected, x_mod.retrieve());
    }
}
