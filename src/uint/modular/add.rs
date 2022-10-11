use core::ops::AddAssign;

use crate::UInt;

use super::Modular;

impl<const LIMBS: usize> AddAssign<&UInt<LIMBS>> for Modular<LIMBS> {
    fn add_assign(&mut self, rhs: &UInt<LIMBS>) {
        *self += &Modular::new(*rhs, self.modulus_params);
    }
}

impl<const LIMBS: usize> AddAssign<&Self> for Modular<LIMBS> {
    fn add_assign(&mut self, rhs: &Self) {
        // TODO: Can we easily verify that these have the same MontgomeryParams? (e.g. using a debug_assert)
        self.value = self.value.add_mod(&rhs.value, &self.modulus_params.modulus);
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        uint::modular::{Modular, MontgomeryParams},
        U256,
    };

    #[test]
    fn add_overflow() {
        let modulus =
            U256::from_be_hex("ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551");
        let modulus_params = MontgomeryParams::new(modulus);

        let x =
            U256::from_be_hex("44acf6b7e36c1342c2c5897204fe09504e1e2efb1a900377dbc4e7a6a133ec56");
        let mut x_mod = Modular::new(x, modulus_params);

        let y =
            U256::from_be_hex("d5777c45019673125ad240f83094d4252d829516fac8601ed01979ec1ec1a251");

        x_mod += &y;

        let expected =
            U256::from_be_hex("1a2472fde50286541d97ca6a3592dd75beb9c9646e40c511b82496cfc3926956");

        assert_eq!(expected, x_mod.retrieve());
    }
}
