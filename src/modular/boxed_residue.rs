//! Implements `BoxedResidue`s, supporting modular arithmetic with a modulus whose size and value
//! is chosen at runtime.

mod add;
mod inv;
mod mul;
mod neg;
mod pow;
mod sub;

use super::reduction::montgomery_reduction_boxed;
use crate::{BoxedUint, Limb, NonZero, Word};
use subtle::CtOption;

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
        let is_odd = modulus.is_odd();

        // Use a surrogate value of `1` in case a modulus of `0` is passed.
        // This will be rejected by the `is_odd` check above, which will fail and return `None`.
        let modulus_nz = NonZero::new(BoxedUint::conditional_select(
            &modulus,
            &BoxedUint::one_with_precision(modulus.bits_precision()),
            modulus.is_zero(),
        ))
        .expect("modulus ensured non-zero");

        let r = BoxedUint::max(bits_precision)
            .rem_vartime(&modulus_nz)
            .wrapping_add(&BoxedUint::one());

        let r2 = r
            .square()
            .rem_vartime(&modulus_nz.widen(bits_precision * 2)) // TODO(tarcieri): constant time
            .shorten(bits_precision);

        // Since we are calculating the inverse modulo (Word::MAX+1),
        // we can take the modulo right away and calculate the inverse of the first limb only.
        let modulus_lo = BoxedUint::from(modulus.limbs.get(0).copied().unwrap_or_default());

        let mod_neg_inv =
            Limb(Word::MIN.wrapping_sub(modulus_lo.inv_mod2k(Word::BITS as usize).limbs[0].0));

        let r3 = montgomery_reduction_boxed(&mut r2.square(), &modulus, mod_neg_inv);

        let params = Self {
            modulus,
            r,
            r2,
            r3,
            mod_neg_inv,
        };

        CtOption::new(params, is_odd)
    }

    /// Modulus value.
    pub fn modulus(&self) -> &BoxedUint {
        &self.modulus
    }

    /// Bits of precision in the modulus.
    pub fn bits_precision(&self) -> usize {
        self.modulus.bits_precision()
    }
}

/// A residue represented using heap-allocated limbs.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct BoxedResidue {
    /// Value in the Montgomery domain.
    montgomery_form: BoxedUint,
    /// Residue parameters.
    residue_params: BoxedResidueParams,
}

impl BoxedResidue {
    /// Instantiates a new [`BoxedResidue`] that represents an integer modulo the provided params.
    pub fn new(integer: &BoxedUint, residue_params: BoxedResidueParams) -> Self {
        debug_assert_eq!(integer.bits_precision(), residue_params.bits_precision());

        let mut product = integer.mul_wide(&residue_params.r2);
        let montgomery_form = montgomery_reduction_boxed(
            &mut product,
            &residue_params.modulus,
            residue_params.mod_neg_inv,
        );

        #[cfg(feature = "zeroize")]
        product.zeroize();

        Self {
            montgomery_form,
            residue_params,
        }
    }

    /// Bits of precision in the modulus.
    pub fn bits_precision(&self) -> usize {
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

        ret
    }

    /// Instantiates a new `Residue` that represents zero.
    pub fn zero(residue_params: BoxedResidueParams) -> Self {
        Self {
            montgomery_form: BoxedUint::zero_with_precision(residue_params.bits_precision()),
            residue_params,
        }
    }

    /// Instantiates a new `Residue` that represents 1.
    pub fn one(residue_params: BoxedResidueParams) -> Self {
        Self {
            montgomery_form: residue_params.r.clone(),
            residue_params,
        }
    }

    /// Returns the parameter struct used to initialize this residue.
    pub fn params(&self) -> &BoxedResidueParams {
        &self.residue_params
    }

    /// Access the `DynResidue` value in Montgomery form.
    pub fn as_montgomery(&self) -> &BoxedUint {
        &self.montgomery_form
    }

    /// Create a `DynResidue` from a value in Montgomery form.
    pub fn from_montgomery(integer: BoxedUint, residue_params: BoxedResidueParams) -> Self {
        debug_assert_eq!(integer.bits_precision(), residue_params.bits_precision());
        Self {
            montgomery_form: integer,
            residue_params,
        }
    }

    /// Extract the value from the `DynResidue` in Montgomery form.
    pub fn to_montgomery(&self) -> BoxedUint {
        self.montgomery_form.clone()
    }
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
