//! Multiplications between boxed residues.

use super::{montgomery_reduction_boxed_mut, BoxedResidue};
use crate::traits::Square;
use crate::{BoxedUint, Limb};
use core::ops::{Mul, MulAssign};

impl BoxedResidue {
    /// Multiplies by `rhs`.
    pub fn mul(&self, rhs: &Self) -> Self {
        debug_assert_eq!(&self.residue_params, &rhs.residue_params);

        Self {
            montgomery_form: mul_montgomery_form(
                &self.montgomery_form,
                &rhs.montgomery_form,
                &self.residue_params.modulus,
                self.residue_params.mod_neg_inv,
            ),
            residue_params: self.residue_params.clone(),
        }
    }

    /// Computes the (reduced) square of a residue.
    pub fn square(&self) -> Self {
        Self {
            montgomery_form: square_montgomery_form(
                &self.montgomery_form,
                &self.residue_params.modulus,
                self.residue_params.mod_neg_inv,
            ),
            residue_params: self.residue_params.clone(),
        }
    }
}

impl Mul<&BoxedResidue> for &BoxedResidue {
    type Output = BoxedResidue;
    fn mul(self, rhs: &BoxedResidue) -> BoxedResidue {
        self.mul(rhs)
    }
}

impl Mul<BoxedResidue> for &BoxedResidue {
    type Output = BoxedResidue;
    #[allow(clippy::op_ref)]
    fn mul(self, rhs: BoxedResidue) -> BoxedResidue {
        self * &rhs
    }
}

impl Mul<&BoxedResidue> for BoxedResidue {
    type Output = BoxedResidue;
    #[allow(clippy::op_ref)]
    fn mul(self, rhs: &BoxedResidue) -> BoxedResidue {
        &self * rhs
    }
}

impl Mul<BoxedResidue> for BoxedResidue {
    type Output = BoxedResidue;
    fn mul(self, rhs: BoxedResidue) -> BoxedResidue {
        &self * &rhs
    }
}

impl MulAssign<&BoxedResidue> for BoxedResidue {
    fn mul_assign(&mut self, rhs: &BoxedResidue) {
        debug_assert_eq!(&self.residue_params, &rhs.residue_params);

        self.montgomery_form = mul_montgomery_form(
            &self.montgomery_form,
            &rhs.montgomery_form,
            &self.residue_params.modulus,
            self.residue_params.mod_neg_inv,
        );
    }
}

impl MulAssign<BoxedResidue> for BoxedResidue {
    fn mul_assign(&mut self, rhs: BoxedResidue) {
        Self::mul_assign(self, &rhs)
    }
}

impl Square for BoxedResidue {
    fn square(&self) -> Self {
        BoxedResidue::square(self)
    }
}

pub(super) fn mul_montgomery_form(
    a: &BoxedUint,
    b: &BoxedUint,
    modulus: &BoxedUint,
    mod_neg_inv: Limb,
) -> BoxedUint {
    let mut ret = a.clone();
    mul_montgomery_form_assign(&mut ret, b, modulus, mod_neg_inv);
    ret
}

pub(super) fn mul_montgomery_form_assign(
    a: &mut BoxedUint,
    b: &BoxedUint,
    modulus: &BoxedUint,
    mod_neg_inv: Limb,
) {
    debug_assert_eq!(a.bits_precision(), modulus.bits_precision());
    debug_assert_eq!(b.bits_precision(), modulus.bits_precision());

    let mut product = a.mul(b);
    montgomery_reduction_boxed_mut(&mut product, modulus, mod_neg_inv, a);

    #[cfg(feature = "zeroize")]
    zeroize::Zeroize::zeroize(&mut product);
}

#[inline]
pub(super) fn square_montgomery_form(
    a: &BoxedUint,
    modulus: &BoxedUint,
    mod_neg_inv: Limb,
) -> BoxedUint {
    let mut ret = a.clone();
    square_montgomery_form_assign(&mut ret, modulus, mod_neg_inv);
    ret
}

#[inline]
pub(super) fn square_montgomery_form_assign(
    a: &mut BoxedUint,
    modulus: &BoxedUint,
    mod_neg_inv: Limb,
) {
    debug_assert_eq!(a.bits_precision(), modulus.bits_precision());

    let mut square = a.square();
    montgomery_reduction_boxed_mut(&mut square, modulus, mod_neg_inv, a);

    #[cfg(feature = "zeroize")]
    zeroize::Zeroize::zeroize(&mut square);
}
