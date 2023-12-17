//! Implements `BoxedResidue`s, supporting modular arithmetic with a modulus whose size and value
//! is chosen at runtime.

mod add;
mod inv;
mod mul;
mod neg;
mod pow;
mod sub;

use super::{
    reduction::{montgomery_reduction_boxed, montgomery_reduction_boxed_mut},
    Retrieve,
};
use crate::{BoxedUint, ConstantTimeSelect, Integer, Limb, NonZero, Word};
use subtle::CtOption;

#[cfg(feature = "std")]
use std::sync::Arc;

#[cfg(feature = "zeroize")]
use zeroize::Zeroize;

/// Parameters to efficiently go to/from the Montgomery form for an odd modulus whose size and value
/// are both chosen at runtime.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct BoxedResidueParams {
    /// The constant modulus
    modulus: BoxedUint,
    /// Parameter used in Montgomery reduction
    r: BoxedUint,
    /// R^2, used to move into Montgomery form
    r2: BoxedUint,
    /// R^3, used to compute the multiplicative inverse
    r3: BoxedUint,
    /// The lowest limbs of -(MODULUS^-1) mod R
    /// We only need the LSB because during reduction this value is multiplied modulo 2**Limb::BITS.
    mod_neg_inv: Limb,
}

impl BoxedResidueParams {
    /// Instantiates a new set of [`BoxedResidueParams`] representing the given `modulus`, which
    /// must be odd.
    ///
    /// Returns a `CtOption` that is `None` if the provided modulus is not odd.
    /// TODO(tarcieri): DRY out with `DynResidueParams::new`?
    pub fn new(modulus: BoxedUint) -> CtOption<Self> {
        let bits_precision = modulus.bits_precision();

        // Use a surrogate value of `1` in case a modulus of `0` is passed.
        // This will be rejected by the `is_odd` check above, which will fail and return `None`.
        let modulus_nz = NonZero::new(BoxedUint::ct_select(
            &modulus,
            &BoxedUint::one_with_precision(bits_precision),
            modulus.is_zero(),
        ))
        .expect("modulus ensured non-zero");

        let r = BoxedUint::max(bits_precision)
            .rem(&modulus_nz)
            .wrapping_add(&BoxedUint::one());

        let r2 = r
            .square()
            .rem(&modulus_nz.widen(bits_precision * 2))
            .shorten(bits_precision);

        Self::new_inner(modulus, r, r2)
    }

    /// Instantiates a new set of [`BoxedResidueParams`] representing the given `modulus`, which
    /// must be odd. This version operates in variable-time with respect to the modulus.
    ///
    /// Returns `None` if the provided modulus is not odd.
    /// TODO(tarcieri): DRY out with `DynResidueParams::new`?
    pub fn new_vartime(modulus: BoxedUint) -> Option<Self> {
        if modulus.is_even().into() {
            return None;
        }

        let bits_precision = modulus.bits_precision();

        // Use a surrogate value of `1` in case a modulus of `0` is passed.
        // This will be rejected by the `is_odd` check above, which will fail and return `None`.
        let modulus_nz = NonZero::new(BoxedUint::ct_select(
            &modulus,
            &BoxedUint::one_with_precision(bits_precision),
            modulus.is_zero(),
        ))
        .expect("modulus ensured non-zero");

        let r = BoxedUint::max(bits_precision)
            .rem_vartime(&modulus_nz)
            .wrapping_add(&BoxedUint::one());

        let r2 = r.square();
        let r2 = r2
            .rem_vartime(&modulus_nz.widen(bits_precision * 2))
            .widen(bits_precision);

        Self::new_inner(modulus, r, r2).into()
    }

    /// Common functionality of `new` and `new_vartime`.
    fn new_inner(modulus: BoxedUint, r: BoxedUint, r2: BoxedUint) -> CtOption<Self> {
        debug_assert_eq!(r.bits_precision(), modulus.bits_precision());
        debug_assert_eq!(r2.bits_precision(), modulus.bits_precision());

        // If the inverse exists, it means the modulus is odd.
        let (inv_mod_limb, modulus_is_odd) = modulus.inv_mod2k(Word::BITS);
        let mod_neg_inv = Limb(Word::MIN.wrapping_sub(inv_mod_limb.limbs[0].0));
        let r3 = montgomery_reduction_boxed(&mut r2.square(), &modulus, mod_neg_inv);

        let params = Self {
            modulus,
            r,
            r2,
            r3,
            mod_neg_inv,
        };

        CtOption::new(params, modulus_is_odd)
    }

    /// Modulus value.
    pub fn modulus(&self) -> &BoxedUint {
        &self.modulus
    }

    /// Bits of precision in the modulus.
    pub fn bits_precision(&self) -> u32 {
        self.modulus.bits_precision()
    }
}

/// A residue represented using heap-allocated limbs.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct BoxedResidue {
    /// Value in the Montgomery domain.
    montgomery_form: BoxedUint,

    /// Residue parameters.
    #[cfg(not(feature = "std"))]
    residue_params: BoxedResidueParams,

    /// Residue parameters.
    // Uses `Arc` when `std` is available.
    #[cfg(feature = "std")]
    residue_params: Arc<BoxedResidueParams>,
}

impl BoxedResidue {
    /// Instantiates a new [`BoxedResidue`] that represents an integer modulo the provided params.
    pub fn new(mut integer: BoxedUint, residue_params: BoxedResidueParams) -> Self {
        debug_assert_eq!(integer.bits_precision(), residue_params.bits_precision());
        convert_to_montgomery(&mut integer, &residue_params);

        #[allow(clippy::useless_conversion)]
        Self {
            montgomery_form: integer,
            residue_params: residue_params.into(),
        }
    }

    /// Instantiates a new [`BoxedResidue`] that represents an integer modulo the provided params.
    #[cfg(feature = "std")]
    pub fn new_with_arc(mut integer: BoxedUint, residue_params: Arc<BoxedResidueParams>) -> Self {
        debug_assert_eq!(integer.bits_precision(), residue_params.bits_precision());
        convert_to_montgomery(&mut integer, &residue_params);
        Self {
            montgomery_form: integer,
            residue_params,
        }
    }

    /// Bits of precision in the modulus.
    pub fn bits_precision(&self) -> u32 {
        self.residue_params.bits_precision()
    }

    /// Retrieves the integer currently encoded in this [`BoxedResidue`], guaranteed to be reduced.
    pub fn retrieve(&self) -> BoxedUint {
        let mut montgomery_form = self.montgomery_form.widen(self.bits_precision() * 2);

        let ret = montgomery_reduction_boxed(
            &mut montgomery_form,
            &self.residue_params.modulus,
            self.residue_params.mod_neg_inv,
        );

        #[cfg(feature = "zeroize")]
        montgomery_form.zeroize();

        debug_assert!(ret < self.residue_params.modulus);
        ret
    }

    /// Instantiates a new `Residue` that represents zero.
    pub fn zero(residue_params: BoxedResidueParams) -> Self {
        Self {
            montgomery_form: BoxedUint::zero_with_precision(residue_params.bits_precision()),
            residue_params: residue_params.into(),
        }
    }

    /// Instantiates a new `Residue` that represents 1.
    pub fn one(residue_params: BoxedResidueParams) -> Self {
        Self {
            montgomery_form: residue_params.r.clone(),
            residue_params: residue_params.into(),
        }
    }

    /// Returns the parameter struct used to initialize this residue.
    pub fn params(&self) -> &BoxedResidueParams {
        &self.residue_params
    }

    /// Access the [`BoxedResidue`] value in Montgomery form.
    pub fn as_montgomery(&self) -> &BoxedUint {
        debug_assert!(self.montgomery_form < self.residue_params.modulus);
        &self.montgomery_form
    }

    /// Create a [`BoxedResidue`] from a value in Montgomery form.
    pub fn from_montgomery(integer: BoxedUint, residue_params: BoxedResidueParams) -> Self {
        debug_assert_eq!(integer.bits_precision(), residue_params.bits_precision());
        Self {
            montgomery_form: integer,
            residue_params: residue_params.into(),
        }
    }

    /// Extract the value from the [`BoxedResidue`] in Montgomery form.
    pub fn to_montgomery(&self) -> BoxedUint {
        debug_assert!(self.montgomery_form < self.residue_params.modulus);
        self.montgomery_form.clone()
    }
}

impl Retrieve for BoxedResidue {
    type Output = BoxedUint;
    fn retrieve(&self) -> BoxedUint {
        self.retrieve()
    }
}

/// Convert the given integer into the Montgomery domain.
#[inline]
fn convert_to_montgomery(integer: &mut BoxedUint, residue_params: &BoxedResidueParams) {
    let mut product = integer.mul(&residue_params.r2);
    montgomery_reduction_boxed_mut(
        &mut product,
        &residue_params.modulus,
        residue_params.mod_neg_inv,
        integer,
    );

    #[cfg(feature = "zeroize")]
    product.zeroize();
}

#[cfg(test)]
mod tests {
    use super::{BoxedResidueParams, BoxedUint};

    #[test]
    fn new_params_with_invalid_modulus() {
        // 0
        let ret = BoxedResidueParams::new(BoxedUint::zero());
        assert!(bool::from(ret.is_none()));

        // 2
        let ret = BoxedResidueParams::new(BoxedUint::from(2u8));
        assert!(bool::from(ret.is_none()));
    }

    #[test]
    fn new_params_with_valid_modulus() {
        BoxedResidueParams::new(BoxedUint::from(3u8)).unwrap();
    }
}
