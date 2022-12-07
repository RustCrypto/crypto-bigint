use core::ops::Neg;

use crate::modular::neg::neg_montgomery_form;

use super::DynResidue;

impl<const LIMBS: usize> Neg for DynResidue<LIMBS> {
    type Output = Self;

    fn neg(self) -> Self {
        DynResidue {
            montgomery_form: neg_montgomery_form(
                &self.montgomery_form,
                &self.residue_params.modulus,
            ),
            residue_params: self.residue_params,
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        modular::runtime_mod::{DynResidue, DynResidueParams},
        U256,
    };

    #[test]
    fn neg() {
        let params = DynResidueParams::new(U256::from_be_hex(
            "ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551",
        ));

        let x =
            U256::from_be_hex("44acf6b7e36c1342c2c5897204fe09504e1e2efb1a900377dbc4e7a6a133ec56");
        let mut x_mod = DynResidue::new(x, params);

        x_mod = -x_mod;

        let expected =
            U256::from_be_hex("bb5309471c93ecbe3d3a768dfb01f6af6ec8cbb28c879b0d17f4e31c5b2f38fb");

        assert_eq!(expected, x_mod.retrieve());
    }
}
