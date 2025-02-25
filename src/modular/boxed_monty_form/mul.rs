//! Multiplication between boxed integers in Montgomery form (i.e. Montgomery multiplication).
//!
//! Some parts adapted from `monty.rs` in `num-bigint`:
//! <https://github.com/rust-num/num-bigint/blob/2cea7f4/src/biguint/monty.rs>
//!
//! Originally (c) 2014 The Rust Project Developers, dual licensed Apache 2.0+MIT.

use super::{BoxedMontyForm, BoxedMontyParams};
use crate::{
    BoxedUint, Limb, Square, SquareAssign, low_level::almost_montgomery_mul::almost_montgomery_mul,
};
use core::{
    borrow::Borrow,
    ops::{Mul, MulAssign},
};

#[cfg(feature = "zeroize")]
use zeroize::Zeroize;

impl BoxedMontyForm {
    /// Multiplies by `rhs`.
    pub fn mul(&self, rhs: &Self) -> Self {
        debug_assert_eq!(&self.params, &rhs.params);
        let montgomery_form = MontyMultiplier::from(self.params.borrow())
            .mul(&self.montgomery_form, &rhs.montgomery_form);

        Self {
            montgomery_form,
            params: self.params.clone(),
        }
    }

    /// Computes the (reduced) square.
    pub fn square(&self) -> Self {
        let montgomery_form =
            MontyMultiplier::from(self.params.borrow()).square(&self.montgomery_form);

        Self {
            montgomery_form,
            params: self.params.clone(),
        }
    }
}

impl Mul<&BoxedMontyForm> for &BoxedMontyForm {
    type Output = BoxedMontyForm;
    fn mul(self, rhs: &BoxedMontyForm) -> BoxedMontyForm {
        self.mul(rhs)
    }
}

impl Mul<BoxedMontyForm> for &BoxedMontyForm {
    type Output = BoxedMontyForm;
    #[allow(clippy::op_ref)]
    fn mul(self, rhs: BoxedMontyForm) -> BoxedMontyForm {
        self * &rhs
    }
}

impl Mul<&BoxedMontyForm> for BoxedMontyForm {
    type Output = BoxedMontyForm;
    #[allow(clippy::op_ref)]
    fn mul(self, rhs: &BoxedMontyForm) -> BoxedMontyForm {
        &self * rhs
    }
}

impl Mul<BoxedMontyForm> for BoxedMontyForm {
    type Output = BoxedMontyForm;
    fn mul(self, rhs: BoxedMontyForm) -> BoxedMontyForm {
        &self * &rhs
    }
}

impl MulAssign<BoxedMontyForm> for BoxedMontyForm {
    fn mul_assign(&mut self, rhs: BoxedMontyForm) {
        Self::mul_assign(self, &rhs)
    }
}

impl MulAssign<&BoxedMontyForm> for BoxedMontyForm {
    fn mul_assign(&mut self, rhs: &BoxedMontyForm) {
        debug_assert_eq!(&self.params, &rhs.params);
        MontyMultiplier::from(self.params.borrow())
            .mul_assign(&mut self.montgomery_form, &rhs.montgomery_form);
    }
}

impl Square for BoxedMontyForm {
    fn square(&self) -> Self {
        BoxedMontyForm::square(self)
    }
}

impl SquareAssign for BoxedMontyForm {
    fn square_assign(&mut self) {
        MontyMultiplier::from(self.params.borrow()).square_assign(&mut self.montgomery_form);
    }
}

impl<'a> From<&'a BoxedMontyParams> for MontyMultiplier<'a> {
    fn from(params: &'a BoxedMontyParams) -> MontyMultiplier<'a> {
        MontyMultiplier::new(&params.modulus, params.mod_neg_inv)
    }
}

/// Montgomery multiplier with a pre-allocated internal buffer to avoid additional allocations.
pub(super) struct MontyMultiplier<'a> {
    product: BoxedUint,
    modulus: &'a BoxedUint,
    mod_neg_inv: Limb,
}

impl<'a> MontyMultiplier<'a> {
    /// Create a new Montgomery multiplier.
    pub(super) fn new(modulus: &'a BoxedUint, mod_neg_inv: Limb) -> Self {
        Self {
            product: BoxedUint::zero_with_precision(modulus.bits_precision() * 2),
            modulus,
            mod_neg_inv,
        }
    }

    /// Perform a Montgomery multiplication, returning a fully reduced result.
    pub(super) fn mul(&mut self, a: &BoxedUint, b: &BoxedUint) -> BoxedUint {
        let mut ret = a.clone();
        self.mul_assign(&mut ret, b);
        ret
    }

    /// Perform a Montgomery multiplication, assigning a fully reduced result to `a`.
    pub(super) fn mul_assign(&mut self, a: &mut BoxedUint, b: &BoxedUint) {
        self.mul_amm_assign(a, b);
        a.sub_assign_mod_with_carry(Limb::ZERO, self.modulus, self.modulus);

        debug_assert!(&*a < self.modulus);
    }

    /// Perform a squaring using Montgomery multiplication, returning a fully reduced result.
    pub(super) fn square(&mut self, a: &BoxedUint) -> BoxedUint {
        let mut ret = a.clone();
        self.square_assign(&mut ret);
        ret
    }

    /// Perform a squaring using Montgomery multiplication, assigning a fully reduced result to `a`.
    pub(super) fn square_assign(&mut self, a: &mut BoxedUint) {
        self.square_amm_assign(a);
        a.sub_assign_mod_with_carry(Limb::ZERO, self.modulus, self.modulus);

        debug_assert!(&*a < self.modulus);
    }

    /// Perform an "Almost Montgomery Multiplication".
    ///
    /// NOTE: the resulting output will be reduced to the *bit length* of the modulus, but not fully reduced and may
    /// exceed the modulus. A final reduction is required to ensure AMM results are fully reduced, and should not be
    /// exposed outside the internals of this crate.
    pub(super) fn mul_amm(&mut self, a: &BoxedUint, b: &BoxedUint) -> BoxedUint {
        let mut ret = a.clone();
        self.mul_amm_assign(&mut ret, b);
        ret
    }

    /// Perform an "Almost Montgomery Multiplication", assigning the product to `a`.
    ///
    /// NOTE: the resulting output will be reduced to the *bit length* of the modulus, but not fully reduced and may
    /// exceed the modulus. A final reduction is required to ensure AMM results are fully reduced, and should not be
    /// exposed outside the internals of this crate.
    pub(super) fn mul_amm_assign(&mut self, a: &mut BoxedUint, b: &BoxedUint) {
        debug_assert_eq!(a.bits_precision(), self.modulus.bits_precision());
        debug_assert_eq!(b.bits_precision(), self.modulus.bits_precision());

        self.clear_product();
        almost_montgomery_mul(
            self.product.as_limbs_mut(),
            a.as_limbs(),
            b.as_limbs(),
            self.modulus.as_limbs(),
            self.mod_neg_inv,
        );
        a.limbs
            .copy_from_slice(&self.product.limbs[..a.limbs.len()]);
    }

    /// Perform a squaring using "Almost Montgomery Multiplication".
    ///
    /// NOTE: the resulting output will be reduced to the *bit length* of the modulus, but not fully reduced and may
    /// exceed the modulus. A final reduction is required to ensure AMM results are fully reduced, and should not be
    /// exposed outside the internals of this crate.
    #[allow(dead_code)] // TODO(tarcieri): use this?
    pub(super) fn square_amm(&mut self, a: &BoxedUint) -> BoxedUint {
        let mut ret = a.clone();
        self.square_amm_assign(&mut ret);
        ret
    }

    /// Perform a squaring using "Almost Montgomery Multiplication", assigning the result to `a`.
    ///
    /// NOTE: the resulting output will be reduced to the *bit length* of the modulus, but not fully reduced and may
    /// exceed the modulus. A final reduction is required to ensure AMM results are fully reduced, and should not be
    /// exposed outside the internals of this crate.
    pub(super) fn square_amm_assign(&mut self, a: &mut BoxedUint) {
        debug_assert_eq!(a.bits_precision(), self.modulus.bits_precision());

        // TODO(tarcieri): optimized implementation
        self.clear_product();
        almost_montgomery_mul(
            self.product.as_limbs_mut(),
            a.as_limbs(),
            a.as_limbs(),
            self.modulus.as_limbs(),
            self.mod_neg_inv,
        );
        a.limbs
            .copy_from_slice(&self.product.limbs[..a.limbs.len()]);
    }

    /// Clear the internal product buffer.
    fn clear_product(&mut self) {
        self.product
            .limbs
            .iter_mut()
            .for_each(|limb| *limb = Limb::ZERO);
    }
}

#[cfg(feature = "zeroize")]
impl Drop for MontyMultiplier<'_> {
    fn drop(&mut self) {
        self.product.zeroize();
    }
}

#[cfg(test)]
mod tests {
    use super::{BoxedMontyForm, BoxedMontyParams, BoxedUint};

    /// Regression test for RustCrypto/crypto-bigint#441
    #[test]
    fn square() {
        let x = 0x20u128;
        let modulus = 0xB44677037A7DBDE04814256570DCBD8Du128;

        let boxed_modulus = BoxedUint::from(modulus);
        let boxed_params = BoxedMontyParams::new(boxed_modulus.to_odd().unwrap());
        let boxed_monty = BoxedMontyForm::new(BoxedUint::from(x), boxed_params);
        let boxed_square = boxed_monty.square();

        // TODO(tarcieri): test for correct output
        assert!(boxed_square.as_montgomery() < boxed_square.params().modulus());
    }
}
