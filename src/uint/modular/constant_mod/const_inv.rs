use core::marker::PhantomData;

use subtle::{Choice, CtOption};

use crate::{
    modular::{inv::inv_montgomery_form, InvResidue},
    Word,
};

use super::{Residue, ResidueParams};

impl<MOD: ResidueParams<LIMBS>, const LIMBS: usize> InvResidue for Residue<MOD, LIMBS> {
    fn inv(self) -> CtOption<Self> {
        let (montgomery_form, error) = inv_montgomery_form(
            self.montgomery_form,
            MOD::MODULUS,
            &MOD::R3,
            MOD::MOD_NEG_INV,
        );

        let value = Self {
            montgomery_form,
            phantom: PhantomData,
        };

        CtOption::new(value, Choice::from((error == Word::MAX) as u8))
    }
}

impl<MOD: ResidueParams<LIMBS>, const LIMBS: usize> Residue<MOD, LIMBS> {
    /// Computes the residue `self^-1` representing the multiplicative inverse of `self`. I.e. `self * self^-1 = 1`. Panics if `self` was not invertible.
    pub const fn inv(self) -> Self {
        let (montgomery_form, error) = inv_montgomery_form(
            self.montgomery_form,
            MOD::MODULUS,
            &MOD::R3,
            MOD::MOD_NEG_INV,
        );

        assert!(error == Word::MAX);

        Self {
            montgomery_form,
            phantom: PhantomData,
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{const_residue, impl_modulus, modular::constant_mod::ResidueParams, U256};

    impl_modulus!(
        Modulus,
        U256,
        "15477BCCEFE197328255BFA79A1217899016D927EF460F4FF404029D24FA4409"
    );

    #[test]
    fn test_self_inverse() {
        let x =
            U256::from_be_hex("77117F1273373C26C700D076B3F780074D03339F56DD0EFB60E7F58441FD3685");
        let x_mod = const_residue!(x, Modulus);

        let inv = x_mod.inv();
        let res = &x_mod * &inv;

        assert_eq!(res.retrieve(), U256::ONE);
    }
}
