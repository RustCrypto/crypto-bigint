//! Multiplication between boxed integers in Montgomery form (i.e. Montgomery multiplication).
//!
//! Some parts adapted from `monty.rs` in `num-bigint`:
//! <https://github.com/rust-num/num-bigint/blob/2cea7f4/src/biguint/monty.rs>
//!
//! Originally (c) 2014 The Rust Project Developers, dual licensed Apache 2.0+MIT.

use super::{BoxedMontyForm, BoxedMontyParams};
use crate::{
    modular::reduction::montgomery_reduction_boxed_mut, uint::mul::mul_limbs, BoxedUint, Limb,
    Square, SquareAssign, Word, Zero,
};
use core::{
    borrow::Borrow,
    ops::{Mul, MulAssign},
};
use subtle::{ConditionallySelectable, ConstantTimeLess};

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
        debug_assert_eq!(a.bits_precision(), self.modulus.bits_precision());
        debug_assert_eq!(b.bits_precision(), self.modulus.bits_precision());

        mul_limbs(&a.limbs, &b.limbs, &mut self.product.limbs);
        montgomery_reduction_boxed_mut(&mut self.product, self.modulus, self.mod_neg_inv, a);

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
        debug_assert_eq!(a.bits_precision(), self.modulus.bits_precision());

        // TODO(tarcieri): optimized implementation
        mul_limbs(&a.limbs, &a.limbs, &mut self.product.limbs);
        montgomery_reduction_boxed_mut(&mut self.product, self.modulus, self.mod_neg_inv, a);

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

/// Compute an "Almost Montgomery Multiplication (AMM)" as described in the paper
/// "Efficient Software Implementations of Modular Exponentiation"
/// <https://eprint.iacr.org/2011/239.pdf>
///
/// Computes z mod m = x * y * 2 ** (-n*_W) mod m assuming k = -1/m mod 2**_W.
///
/// x and y are required to satisfy 0 <= z < 2**(n*_W) and then the result z is guaranteed to
/// satisfy 0 <= z < 2**(n*_W), but it may not be < m.
///
/// Output is written into the lower (i.e. first) half of `z`.
///
/// Note: this was adapted from an implementation in `num-bigint`'s `monty.rs`.
// TODO(tarcieri): refactor into `reduction.rs`, share impl with `MontyForm`?
fn almost_montgomery_mul(z: &mut [Limb], x: &[Limb], y: &[Limb], m: &[Limb], k: Limb) {
    // This code assumes x, y, m are all the same length (required by addMulVVW and the for loop).
    // It also assumes that x, y are already reduced mod m, or else the result will not be properly
    // reduced.
    let n = m.len();

    // This preconditions check allows compiler to remove bound checks later in the code.
    // `z.len() > n && z[n..].len() == n` is used intentionally instead of `z.len() == 2* n`
    // since the latter prevents compiler from removing some bound checks.
    let pre_cond = z.len() > n && z[n..].len() == n && x.len() == n && y.len() == n && m.len() == n;
    if !pre_cond {
        panic!("Failed preconditions in montgomery_mul");
    }

    let mut c = Limb::ZERO;

    for i in 0..n {
        let c2 = add_mul_vvw(&mut z[i..n + i], x, y[i]);
        let t = z[i].wrapping_mul(k);
        let c3 = add_mul_vvw(&mut z[i..n + i], m, t);
        let cx = c.wrapping_add(c2);
        let cy = cx.wrapping_add(c3);
        z[n + i] = cy;
        c = Limb((cx.ct_lt(&c2) | cy.ct_lt(&c3)).unwrap_u8() as Word);
    }

    let (lower, upper) = z.split_at_mut(n);
    sub_vv(lower, upper, m);

    let is_zero = c.is_zero();
    for (a, b) in lower.iter_mut().zip(upper.iter()) {
        a.conditional_assign(b, is_zero);
    }
}

#[inline]
fn add_mul_vvw(z: &mut [Limb], x: &[Limb], y: Limb) -> Limb {
    let mut c = Limb::ZERO;
    for (zi, xi) in z.iter_mut().zip(x.iter()) {
        let (z0, z1) = zi.mac(*xi, y, Limb::ZERO);
        let (zi_, c_) = z0.overflowing_add(c);
        *zi = zi_;
        c = c_.wrapping_add(z1);
    }

    c
}

#[inline(always)]
fn sub_vv(z: &mut [Limb], x: &[Limb], y: &[Limb]) {
    let mut borrow = Limb::ZERO;
    for (i, (&xi, &yi)) in x.iter().zip(y.iter()).enumerate().take(z.len()) {
        let (zi, new_borrow) = xi.sbb(yi, borrow);
        z[i] = zi;
        borrow = new_borrow;
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
