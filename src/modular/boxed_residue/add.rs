//! Additions between boxed residues.

use super::BoxedMontyForm;
use core::ops::{Add, AddAssign};

impl BoxedMontyForm {
    /// Adds `rhs`.
    pub fn add(&self, rhs: &Self) -> Self {
        debug_assert_eq!(self.residue_params, rhs.residue_params);

        Self {
            montgomery_form: self
                .montgomery_form
                .add_mod(&rhs.montgomery_form, &self.residue_params.modulus),
            residue_params: self.residue_params.clone(),
        }
    }
}

impl Add<&BoxedMontyForm> for &BoxedMontyForm {
    type Output = BoxedMontyForm;
    fn add(self, rhs: &BoxedMontyForm) -> BoxedMontyForm {
        self.add(rhs)
    }
}

impl Add<BoxedMontyForm> for &BoxedMontyForm {
    type Output = BoxedMontyForm;
    #[allow(clippy::op_ref)]
    fn add(self, rhs: BoxedMontyForm) -> BoxedMontyForm {
        self + &rhs
    }
}

impl Add<&BoxedMontyForm> for BoxedMontyForm {
    type Output = BoxedMontyForm;
    #[allow(clippy::op_ref)]
    fn add(self, rhs: &BoxedMontyForm) -> BoxedMontyForm {
        &self + rhs
    }
}

impl Add<BoxedMontyForm> for BoxedMontyForm {
    type Output = BoxedMontyForm;
    fn add(self, rhs: BoxedMontyForm) -> BoxedMontyForm {
        &self + &rhs
    }
}

impl AddAssign<&BoxedMontyForm> for BoxedMontyForm {
    fn add_assign(&mut self, rhs: &BoxedMontyForm) {
        debug_assert_eq!(self.residue_params, rhs.residue_params);
        self.montgomery_form = self
            .montgomery_form
            .add_mod(&rhs.montgomery_form, &self.residue_params.modulus)
    }
}

impl AddAssign<BoxedMontyForm> for BoxedMontyForm {
    fn add_assign(&mut self, rhs: BoxedMontyForm) {
        *self += &rhs;
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        modular::{BoxedMontyForm, BoxedMontyFormParams},
        BoxedUint,
    };
    use hex_literal::hex;

    #[test]
    fn add_overflow() {
        let params = BoxedMontyFormParams::new(
            BoxedUint::from_be_slice(
                &hex!("ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551"),
                256,
            )
            .unwrap(),
        )
        .unwrap();

        let x = BoxedUint::from_be_slice(
            &hex!("44acf6b7e36c1342c2c5897204fe09504e1e2efb1a900377dbc4e7a6a133ec56"),
            256,
        )
        .unwrap();
        let mut x_mod = BoxedMontyForm::new(x, params.clone());

        let y = BoxedUint::from_be_slice(
            &hex!("d5777c45019673125ad240f83094d4252d829516fac8601ed01979ec1ec1a251"),
            256,
        )
        .unwrap();
        let y_mod = BoxedMontyForm::new(y, params.clone());

        x_mod += &y_mod;

        let expected = BoxedUint::from_be_slice(
            &hex!("1a2472fde50286541d97ca6a3592dd75beb9c9646e40c511b82496cfc3926956"),
            256,
        )
        .unwrap();

        assert_eq!(expected, x_mod.retrieve());
    }
}
