//! Negations of integers in Montgomery form with a constant modulus.

use super::{ConstMontyForm, ConstMontyParams};
use core::ops::Neg;

impl<MOD: ConstMontyParams<LIMBS>, const LIMBS: usize> ConstMontyForm<MOD, LIMBS> {
    /// Negates the number.
    pub const fn neg(&self) -> Self {
        Self::ZERO.sub(self)
    }
}

impl<MOD: ConstMontyParams<LIMBS>, const LIMBS: usize> Neg for ConstMontyForm<MOD, LIMBS> {
    type Output = Self;
    fn neg(self) -> Self {
        ConstMontyForm::neg(&self)
    }
}

impl<MOD: ConstMontyParams<LIMBS>, const LIMBS: usize> Neg for &ConstMontyForm<MOD, LIMBS> {
    type Output = ConstMontyForm<MOD, LIMBS>;
    fn neg(self) -> ConstMontyForm<MOD, LIMBS> {
        ConstMontyForm::neg(self)
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        const_monty_form, impl_modulus, modular::const_monty_form::ConstMontyParams, U256,
    };

    impl_modulus!(
        Modulus,
        U256,
        "15477BCCEFE197328255BFA79A1217899016D927EF460F4FF404029D24FA4409"
    );

    #[test]
    fn test_negate() {
        let x =
            U256::from_be_hex("77117F1273373C26C700D076B3F780074D03339F56DD0EFB60E7F58441FD3685");
        let x_mod = const_monty_form!(x, Modulus);

        let res = -x_mod;
        let expected =
            U256::from_be_hex("089B67BB2C124F084701AD76E8750D321385E35044C74CE457301A2A9BE061B1");

        assert_eq!(res.retrieve(), expected);
    }
}
