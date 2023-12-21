//! Multiplicative inverses of boxed integers in Montgomery form.

use super::BoxedMontyForm;
use crate::{modular::reduction::montgomery_reduction_boxed_mut, Invert};
use subtle::CtOption;

impl BoxedMontyForm {
    /// Computes `self^-1` representing the multiplicative inverse of `self`.
    /// I.e. `self * self^-1 = 1`.
    pub fn invert(&self) -> CtOption<Self> {
        let (mut inverse, is_some) = self.montgomery_form.inv_odd_mod(&self.params.modulus);

        let mut product = inverse.mul(&self.params.r3);

        montgomery_reduction_boxed_mut(
            &mut product,
            &self.params.modulus,
            self.params.mod_neg_inv,
            &mut inverse,
        );

        let value = Self {
            montgomery_form: inverse,
            params: self.params.clone(),
        };

        CtOption::new(value, is_some)
    }
}

impl Invert for BoxedMontyForm {
    type Output = CtOption<Self>;
    fn invert(&self) -> Self::Output {
        self.invert()
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        modular::{BoxedMontyForm, BoxedMontyParams},
        BoxedUint,
    };
    use hex_literal::hex;

    fn monty_params() -> BoxedMontyParams {
        BoxedMontyParams::new(
            BoxedUint::from_be_slice(
                &hex!("15477BCCEFE197328255BFA79A1217899016D927EF460F4FF404029D24FA4409"),
                256,
            )
            .unwrap()
            .to_odd()
            .unwrap(),
        )
    }

    #[test]
    fn test_self_inverse() {
        let params = monty_params();
        let x = BoxedUint::from_be_slice(
            &hex!("77117F1273373C26C700D076B3F780074D03339F56DD0EFB60E7F58441FD3685"),
            256,
        )
        .unwrap();
        let x_mod = BoxedMontyForm::new(x, params);

        let inv = x_mod.invert().unwrap();
        let res = x_mod * inv;

        assert!(bool::from(res.retrieve().is_one()));
    }
}
