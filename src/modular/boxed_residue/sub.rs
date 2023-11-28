//! Subtractions between boxed residues.

use super::BoxedResidue;
use core::ops::{Sub, SubAssign};

impl BoxedResidue {
    /// Subtracts `rhs`.
    pub fn sub(&self, rhs: &Self) -> Self {
        debug_assert_eq!(self.residue_params, rhs.residue_params);

        Self {
            montgomery_form: self
                .montgomery_form
                .sub_mod(&rhs.montgomery_form, &self.residue_params.modulus),
            residue_params: self.residue_params.clone(),
        }
    }
}

impl Sub<&BoxedResidue> for &BoxedResidue {
    type Output = BoxedResidue;
    fn sub(self, rhs: &BoxedResidue) -> BoxedResidue {
        debug_assert_eq!(self.residue_params, rhs.residue_params);
        self.sub(rhs)
    }
}

impl Sub<BoxedResidue> for &BoxedResidue {
    type Output = BoxedResidue;
    #[allow(clippy::op_ref)]
    fn sub(self, rhs: BoxedResidue) -> BoxedResidue {
        self - &rhs
    }
}

impl Sub<&BoxedResidue> for BoxedResidue {
    type Output = BoxedResidue;
    #[allow(clippy::op_ref)]
    fn sub(self, rhs: &BoxedResidue) -> BoxedResidue {
        &self - rhs
    }
}

impl Sub<BoxedResidue> for BoxedResidue {
    type Output = BoxedResidue;
    fn sub(self, rhs: BoxedResidue) -> BoxedResidue {
        &self - &rhs
    }
}

impl SubAssign<&BoxedResidue> for BoxedResidue {
    fn sub_assign(&mut self, rhs: &BoxedResidue) {
        debug_assert_eq!(self.residue_params, rhs.residue_params);
        self.montgomery_form = self
            .montgomery_form
            .sub_mod(&rhs.montgomery_form, &self.residue_params.modulus)
    }
}

impl SubAssign<BoxedResidue> for BoxedResidue {
    fn sub_assign(&mut self, rhs: BoxedResidue) {
        *self -= &rhs;
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        modular::{BoxedResidue, BoxedResidueParams},
        BoxedUint,
    };
    use hex_literal::hex;

    #[test]
    fn sub_overflow() {
        let params = BoxedResidueParams::new(
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
        let mut x_mod = BoxedResidue::new(&x, params.clone());

        let y = BoxedUint::from_be_slice(
            &hex!("d5777c45019673125ad240f83094d4252d829516fac8601ed01979ec1ec1a251"),
            256,
        )
        .unwrap();
        let y_mod = BoxedResidue::new(&y, params);

        x_mod -= &y_mod;

        let expected = BoxedUint::from_be_slice(
            &hex!("6f357a71e1d5a03167f34879d469352add829491c6df41ddff65387d7ed56f56"),
            256,
        )
        .unwrap();

        assert_eq!(expected, x_mod.retrieve());
    }
}
