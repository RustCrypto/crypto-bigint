//! Modular exponentiation support for [`BoxedResidue`].

use super::{mul::MontgomeryMultiplier, BoxedResidue};
use crate::{BoxedUint, Limb, PowBoundedExp};
use alloc::vec::Vec;

impl BoxedResidue {
    /// Raises to the `exponent` power.
    pub fn pow(&self, exponent: &BoxedUint) -> Self {
        let ret = self.pow_bounded_exp(exponent, exponent.bits_precision());
        debug_assert!(ret.retrieve() < self.residue_params.modulus);
        ret
    }

    /// Raises to the `exponent` power,
    /// with `exponent_bits` representing the number of (least significant) bits
    /// to take into account for the exponent.
    ///
    /// NOTE: `exponent_bits` may be leaked in the time pattern.
    pub fn pow_bounded_exp(&self, exponent: &BoxedUint, exponent_bits: u32) -> Self {
        Self {
            montgomery_form: pow_montgomery_form(
                &self.montgomery_form,
                exponent,
                exponent_bits,
                &self.residue_params.modulus,
                &self.residue_params.r,
                self.residue_params.mod_neg_inv,
            ),
            residue_params: self.residue_params.clone(),
        }
    }
}

impl PowBoundedExp<BoxedUint> for BoxedResidue {
    fn pow_bounded_exp(&self, exponent: &BoxedUint, exponent_bits: u32) -> Self {
        self.pow_bounded_exp(exponent, exponent_bits)
    }
}

/// Performs modular exponentiation using Montgomery's ladder.
/// `exponent_bits` represents the number of bits to take into account for the exponent.
///
/// NOTE: this value is leaked in the time pattern.
fn pow_montgomery_form(
    x: &BoxedUint,
    exponent: &BoxedUint,
    _exponent_bits: u32,
    modulus: &BoxedUint,
    r: &BoxedUint,
    mod_neg_inv: Limb,
) -> BoxedUint {
    const WINDOW: u32 = 4;

    let mut multiplier = MontgomeryMultiplier::new(modulus, mod_neg_inv);

    // powers[i] contains x^i
    let mut powers = Vec::with_capacity(1 << WINDOW);
    powers.push(r.clone()); // 1 in Montgomery form
    powers.push(x.clone());

    for i in 2..(1 << WINDOW) {
        powers.push(multiplier.mul(&powers[i - 1], x));
    }

    // initialize z = 1 (Montgomery 1)
    let mut z = powers[0].clone();

    // same windowed exponent, but with Montgomery multiplications
    for i in (0..exponent.limbs.len()).rev() {
        let mut yi = exponent.limbs[i];
        let mut j = 0;
        while j < Limb::BITS {
            if i != exponent.limbs.len() - 1 || j != 0 {
                multiplier.square_assign(&mut z);
                multiplier.square_assign(&mut z);
                multiplier.square_assign(&mut z);
                multiplier.square_assign(&mut z);
            }
            multiplier.mul_assign(&mut z, &powers[(yi.0 >> (Limb::BITS - WINDOW)) as usize]);
            yi <<= WINDOW;
            j += WINDOW;
        }
    }

    z
}
