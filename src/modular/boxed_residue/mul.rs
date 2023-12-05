//! Multiplications between boxed residues.

use super::{montgomery_reduction_boxed_mut, BoxedResidue, BoxedResidueParams};
use crate::{traits::Square, uint::mul::mul_limbs, BoxedUint, Limb};
use core::{
    borrow::Borrow,
    ops::{Mul, MulAssign},
};

#[cfg(feature = "zeroize")]
use zeroize::Zeroize;

impl BoxedResidue {
    /// Multiplies by `rhs`.
    pub fn mul(&self, rhs: &Self) -> Self {
        debug_assert_eq!(&self.residue_params, &rhs.residue_params);

        let montgomery_form = MontgomeryMultiplier::from(self.residue_params.borrow())
            .mul(&self.montgomery_form, &rhs.montgomery_form);

        Self {
            montgomery_form,
            residue_params: self.residue_params.clone(),
        }
    }

    /// Computes the (reduced) square of a residue.
    pub fn square(&self) -> Self {
        let montgomery_form =
            MontgomeryMultiplier::from(self.residue_params.borrow()).square(&self.montgomery_form);

        Self {
            montgomery_form,
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
        MontgomeryMultiplier::from(self.residue_params.borrow())
            .mul_assign(&mut self.montgomery_form, &rhs.montgomery_form);
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

impl<'a> From<&'a BoxedResidueParams> for MontgomeryMultiplier<'a> {
    fn from(residue_params: &'a BoxedResidueParams) -> MontgomeryMultiplier<'a> {
        MontgomeryMultiplier::new(&residue_params.modulus, residue_params.mod_neg_inv)
    }
}

/// Montgomery multiplier with a pre-allocated internal buffer to avoid additional allocations.
pub(super) struct MontgomeryMultiplier<'a> {
    product: BoxedUint,
    modulus: &'a BoxedUint,
    mod_neg_inv: Limb,
}

impl<'a> MontgomeryMultiplier<'a> {
    /// Create a new Montgomery multiplier.
    pub(super) fn new(modulus: &'a BoxedUint, mod_neg_inv: Limb) -> Self {
        Self {
            product: BoxedUint::zero_with_precision(modulus.bits_precision() * 2),
            modulus,
            mod_neg_inv,
        }
    }

    /// Multiply two values in Montgomery form.
    pub(super) fn mul(&mut self, a: &BoxedUint, b: &BoxedUint) -> BoxedUint {
        let mut ret = a.clone();
        self.mul_assign(&mut ret, b);
        ret
    }

    /// Multiply two values in Montgomery form, assigning the product to `a`.
    pub(super) fn mul_assign(&mut self, a: &mut BoxedUint, b: &BoxedUint) {
        debug_assert_eq!(a.bits_precision(), self.modulus.bits_precision());
        debug_assert_eq!(b.bits_precision(), self.modulus.bits_precision());

        self.clear_product();
        mul_limbs(&a.limbs, &b.limbs, &mut self.product.limbs);
        self.montgomery_reduction(a);
    }

    /// Square the given value in Montgomery form.
    #[inline]
    pub(super) fn square(&mut self, a: &BoxedUint) -> BoxedUint {
        let mut ret = a.clone();
        self.square_assign(&mut ret);
        ret
    }

    /// Square the given value in Montgomery form, assigning the result to `a`.
    #[inline]
    pub(super) fn square_assign(&mut self, a: &mut BoxedUint) {
        debug_assert_eq!(a.bits_precision(), self.modulus.bits_precision());
        self.clear_product();
        mul_limbs(&a.limbs, &a.limbs, &mut self.product.limbs);
        self.montgomery_reduction(a);
    }

    /// Clear the internal product buffer.
    fn clear_product(&mut self) {
        self.product
            .limbs
            .iter_mut()
            .for_each(|limb| *limb = Limb::ZERO);
    }

    /// Perform Montgomery reduction on the internal product buffer.
    fn montgomery_reduction(&mut self, out: &mut BoxedUint) {
        montgomery_reduction_boxed_mut(&mut self.product, self.modulus, self.mod_neg_inv, out);
    }
}

#[cfg(feature = "zeroize")]
impl Drop for MontgomeryMultiplier<'_> {
    fn drop(&mut self) {
        self.product.zeroize();
    }
}
