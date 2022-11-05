use core::marker::PhantomData;

use crate::modular::inv::{inv_montgomery_form, InvResidue};

use super::{ConstResidue, ConstResidueParams};

impl<MOD: ConstResidueParams<LIMBS>, const LIMBS: usize> InvResidue for ConstResidue<MOD, LIMBS> {
    fn inv(self) -> Self {
        self.inv()
    }
}

impl<MOD: ConstResidueParams<LIMBS>, const LIMBS: usize> ConstResidue<MOD, LIMBS> {
    /// Computes the residue `self^-1` representing the multiplicative inverse of `self`. I.e. `self * self^-1 = 1`.
    pub const fn inv(self) -> Self {
        Self {
            montgomery_form: inv_montgomery_form(
                self.montgomery_form,
                MOD::MODULUS,
                &MOD::R3,
                MOD::MOD_NEG_INV,
            ),
            phantom: PhantomData,
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        const_residue, impl_modulus, modular::constant_mod::ConstResidueParams, traits::Encoding,
        U256,
    };

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
