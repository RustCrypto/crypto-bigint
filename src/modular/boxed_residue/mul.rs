//! Multiplication between boxed residues (i.e. Montgomery multiplication).
//!
//! Some parts adapted from `monty.rs` in `num-bigint`:
//! <https://github.com/rust-num/num-bigint/blob/2cea7f4/src/biguint/monty.rs>
//!
//! Originally (c) 2014 The Rust Project Developers, dual licensed Apache 2.0+MIT.

use super::{BoxedResidue, BoxedResidueParams};
use crate::{traits::Square, BoxedUint, Limb, WideWord, Word};
use core::{
    borrow::Borrow,
    ops::{Mul, MulAssign},
};
use subtle::{ConditionallySelectable, ConstantTimeEq};

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

    /// Perform an "Almost Montgomery Multiplication".
    pub(super) fn mul(&mut self, a: &BoxedUint, b: &BoxedUint) -> BoxedUint {
        let mut ret = a.clone();
        self.mul_assign(&mut ret, b);
        ret
    }

    /// Perform an "Almost Montgomery Multiplication", assigning the product to `a`.
    pub(super) fn mul_assign(&mut self, a: &mut BoxedUint, b: &BoxedUint) {
        debug_assert_eq!(a.bits_precision(), self.modulus.bits_precision());
        debug_assert_eq!(b.bits_precision(), self.modulus.bits_precision());

        self.clear_product();
        montgomery_mul(
            self.product.as_words_mut(),
            a.as_words(),
            b.as_words(),
            self.modulus.as_words(),
            self.mod_neg_inv.into(),
        );
        a.limbs
            .copy_from_slice(&self.product.limbs[..a.limbs.len()]);
    }

    /// Perform a squaring "Almost Montgomery Multiplication".
    pub(super) fn square(&mut self, a: &BoxedUint) -> BoxedUint {
        let mut ret = a.clone();
        self.square_assign(&mut ret);
        ret
    }

    /// Perform a squaring using "Almost Montgomery Multiplication"
    pub(super) fn square_assign(&mut self, a: &mut BoxedUint) {
        debug_assert_eq!(a.bits_precision(), self.modulus.bits_precision());

        self.clear_product();
        montgomery_mul(
            self.product.as_words_mut(),
            a.as_words(),
            a.as_words(),
            self.modulus.as_words(),
            self.mod_neg_inv.into(),
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
impl Drop for MontgomeryMultiplier<'_> {
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
// TODO(tarcieri): refactor into `reduction.rs`, share impl with `(Dyn)Residue`?
#[cfg(feature = "alloc")]
fn montgomery_mul(z: &mut [Word], x: &[Word], y: &[Word], m: &[Word], k: Word) {
    // This code assumes x, y, m are all the same length (required by addMulVVW and the for loop).
    // It also assumes that x, y are already reduced mod m, or else the result will not be properly
    // reduced.
    let n = m.len();
    debug_assert_eq!(z.len(), n * 2);
    debug_assert_eq!(x.len(), n);
    debug_assert_eq!(y.len(), n);
    debug_assert_eq!(m.len(), n);

    let mut c: Word = 0;

    for i in 0..n {
        let c2 = add_mul_vvw(&mut z[i..n + i], x, y[i]);
        let t = z[i].wrapping_mul(k);
        let c3 = add_mul_vvw(&mut z[i..n + i], m, t);
        let cx = c.wrapping_add(c2);
        let cy = cx.wrapping_add(c3);
        z[n + i] = cy;

        // TODO(tarcieri): eliminate data-dependent branches
        c = (cx < c2 || cy < c3) as Word;
    }

    let (lower, upper) = z.split_at_mut(n);
    sub_vv(lower, upper, m);

    let is_zero = c.ct_eq(&0);
    for (a, b) in lower.iter_mut().zip(upper.iter()) {
        a.conditional_assign(b, is_zero);
    }
}

#[inline]
fn add_mul_vvw(z: &mut [Word], x: &[Word], y: Word) -> Word {
    let mut c = 0;
    for (zi, xi) in z.iter_mut().zip(x.iter()) {
        let (z1, z0) = mul_add_www(*xi, y, *zi);
        let (c_, zi_) = add_ww(z0, c, 0);
        *zi = zi_;
        c = c_.wrapping_add(z1);
    }

    c
}

/// The resulting carry c is either 0 or 1.
#[inline(always)]
fn sub_vv(z: &mut [Word], x: &[Word], y: &[Word]) -> Word {
    let mut c = 0;
    for (i, (&xi, &yi)) in x.iter().zip(y.iter()).enumerate().take(z.len()) {
        let zi = xi.wrapping_sub(yi).wrapping_sub(c);
        z[i] = zi;
        // see "Hacker's Delight", section 2-12 (overflow detection)
        c = ((yi & !xi) | ((yi | !xi) & zi)) >> (Word::BITS - 1)
    }

    c
}

/// z1<<_W + z0 = x+y+c, with c == 0 or 1
#[inline(always)]
fn add_ww(x: Word, y: Word, c: Word) -> (Word, Word) {
    let yc = y.wrapping_add(c);
    let z0 = x.wrapping_add(yc);
    let z1 = (z0 < x || yc < y) as Word;
    (z1, z0)
}

/// z1 << _W + z0 = x * y + c
#[inline]
fn mul_add_www(x: Word, y: Word, c: Word) -> (Word, Word) {
    let z = x as WideWord * y as WideWord + c as WideWord;
    ((z >> Word::BITS) as Word, z as Word)
}
