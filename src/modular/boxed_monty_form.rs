//! is chosen at runtime.

mod add;
mod inv;
mod mul;
mod neg;
mod pow;
mod sub;

use super::{
    div_by_2,
    reduction::{montgomery_reduction_boxed, montgomery_reduction_boxed_mut},
    Retrieve,
};
use crate::{BoxedUint, Limb, Monty, Odd, Word};

#[cfg(feature = "std")]
use std::sync::Arc;

#[cfg(feature = "zeroize")]
use zeroize::Zeroize;

/// Parameters to efficiently go to/from the Montgomery form for an odd modulus whose size and value
/// are both chosen at runtime.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct BoxedMontyParams {
    /// The constant modulus
    modulus: Odd<BoxedUint>,
    /// Parameter used in Montgomery reduction
    one: BoxedUint,
    /// R^2, used to move into Montgomery form
    r2: BoxedUint,
    /// R^3, used to compute the multiplicative inverse
    r3: BoxedUint,
    /// The lowest limbs of -(MODULUS^-1) mod R
    /// We only need the LSB because during reduction this value is multiplied modulo 2**Limb::BITS.
    mod_neg_inv: Limb,
}

impl BoxedMontyParams {
    /// Instantiates a new set of [`BoxedMontyParams`] representing the given `modulus`, which
    /// must be odd.
    ///
    /// Returns a `CtOption` that is `None` if the provided modulus is not odd.
    /// TODO(tarcieri): DRY out with `MontyParams::new`?
    pub fn new(modulus: Odd<BoxedUint>) -> Self {
        let bits_precision = modulus.bits_precision();

        // `R mod modulus` where `R = 2^BITS`.
        // Represents 1 in Montgomery form.
        let one = BoxedUint::max(bits_precision)
            .rem(modulus.as_nz_ref())
            .wrapping_add(&BoxedUint::one());

        // `R^2 mod modulus`, used to convert integers to Montgomery form.
        let r2 = one
            .square()
            .rem(&modulus.as_nz_ref().widen(bits_precision * 2))
            .shorten(bits_precision);

        Self::new_inner(modulus, one, r2)
    }

    /// Instantiates a new set of [`BoxedMontyParams`] representing the given `modulus`, which
    /// must be odd. This version operates in variable-time with respect to the modulus.
    ///
    /// Returns `None` if the provided modulus is not odd.
    /// TODO(tarcieri): DRY out with `MontyParams::new`?
    pub fn new_vartime(modulus: Odd<BoxedUint>) -> Self {
        let bits_precision = modulus.bits_precision();

        // `R mod modulus` where `R = 2^BITS`.
        // Represents 1 in Montgomery form.
        let one = BoxedUint::max(bits_precision)
            .rem_vartime(modulus.as_nz_ref())
            .wrapping_add(&BoxedUint::one());

        // `R^2 mod modulus`, used to convert integers to Montgomery form.
        let r2 = one
            .square()
            .rem_vartime(&modulus.as_nz_ref().widen(bits_precision * 2))
            .shorten(bits_precision);

        Self::new_inner(modulus, one, r2)
    }

    /// Common functionality of `new` and `new_vartime`.
    fn new_inner(modulus: Odd<BoxedUint>, one: BoxedUint, r2: BoxedUint) -> Self {
        debug_assert_eq!(one.bits_precision(), modulus.bits_precision());
        debug_assert_eq!(r2.bits_precision(), modulus.bits_precision());

        // If the inverse exists, it means the modulus is odd.
        let (inv_mod_limb, modulus_is_odd) = modulus.inv_mod2k(Word::BITS);
        debug_assert!(bool::from(modulus_is_odd));

        let mod_neg_inv = Limb(Word::MIN.wrapping_sub(inv_mod_limb.limbs[0].0));
        let r3 = montgomery_reduction_boxed(&mut r2.square(), &modulus, mod_neg_inv);

        Self {
            modulus,
            one,
            r2,
            r3,
            mod_neg_inv,
        }
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

/// An integer in Montgomery form represented using heap-allocated limbs.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct BoxedMontyForm {
    /// Value in the Montgomery form.
    montgomery_form: BoxedUint,

    /// Montgomery form parameters.
    #[cfg(not(feature = "std"))]
    params: BoxedMontyParams,

    /// Montgomery form parameters.
    // Uses `Arc` when `std` is available.
    #[cfg(feature = "std")]
    params: Arc<BoxedMontyParams>,
}

impl BoxedMontyForm {
    /// Instantiates a new [`BoxedMontyForm`] that represents an integer modulo the provided params.
    pub fn new(mut integer: BoxedUint, params: BoxedMontyParams) -> Self {
        debug_assert_eq!(integer.bits_precision(), params.bits_precision());
        convert_to_montgomery(&mut integer, &params);

        #[allow(clippy::useless_conversion)]
        Self {
            montgomery_form: integer,
            params: params.into(),
        }
    }

    /// Instantiates a new [`BoxedMontyForm`] that represents an integer modulo the provided params.
    #[cfg(feature = "std")]
    pub fn new_with_arc(mut integer: BoxedUint, params: Arc<BoxedMontyParams>) -> Self {
        debug_assert_eq!(integer.bits_precision(), params.bits_precision());
        convert_to_montgomery(&mut integer, &params);
        Self {
            montgomery_form: integer,
            params,
        }
    }

    /// Bits of precision in the modulus.
    pub fn bits_precision(&self) -> u32 {
        self.params.bits_precision()
    }

    /// Retrieves the integer currently encoded in this [`BoxedMontyForm`], guaranteed to be reduced.
    pub fn retrieve(&self) -> BoxedUint {
        let mut montgomery_form = self.montgomery_form.widen(self.bits_precision() * 2);

        let ret = montgomery_reduction_boxed(
            &mut montgomery_form,
            &self.params.modulus,
            self.params.mod_neg_inv,
        );

        #[cfg(feature = "zeroize")]
        montgomery_form.zeroize();

        debug_assert!(ret < self.params.modulus);
        ret
    }

    /// Instantiates a new `ConstMontyForm` that represents zero.
    pub fn zero(params: BoxedMontyParams) -> Self {
        Self {
            montgomery_form: BoxedUint::zero_with_precision(params.bits_precision()),
            params: params.into(),
        }
    }

    /// Instantiates a new `ConstMontyForm` that represents 1.
    pub fn one(params: BoxedMontyParams) -> Self {
        Self {
            montgomery_form: params.one.clone(),
            params: params.into(),
        }
    }

    /// Returns the parameter struct used to initialize this object.
    pub fn params(&self) -> &BoxedMontyParams {
        &self.params
    }

    /// Access the [`BoxedMontyForm`] value in Montgomery form.
    pub fn as_montgomery(&self) -> &BoxedUint {
        debug_assert!(self.montgomery_form < self.params.modulus);
        &self.montgomery_form
    }

    /// Create a [`BoxedMontyForm`] from a value in Montgomery form.
    pub fn from_montgomery(integer: BoxedUint, params: BoxedMontyParams) -> Self {
        debug_assert_eq!(integer.bits_precision(), params.bits_precision());
        Self {
            montgomery_form: integer,
            params: params.into(),
        }
    }

    /// Extract the value from the [`BoxedMontyForm`] in Montgomery form.
    pub fn to_montgomery(&self) -> BoxedUint {
        debug_assert!(self.montgomery_form < self.params.modulus);
        self.montgomery_form.clone()
    }

    /// Performs the modular division by 2, that is for given `x` returns `y`
    /// such that `y * 2 = x mod p`. This means:
    /// - if `x` is even, returns `x / 2`,
    /// - if `x` is odd, returns `(x + p) / 2`
    ///   (since the modulus `p` in Montgomery form is always odd, this divides entirely).
    pub fn div_by_2(&self) -> Self {
        Self {
            montgomery_form: div_by_2::boxed::div_by_2(&self.montgomery_form, &self.params.modulus),
            params: self.params.clone(),
        }
    }
}

impl Retrieve for BoxedMontyForm {
    type Output = BoxedUint;
    fn retrieve(&self) -> BoxedUint {
        self.retrieve()
    }
}

impl Monty for BoxedMontyForm {
    type Integer = BoxedUint;
    type Params = BoxedMontyParams;

    fn new_params(modulus: Odd<Self::Integer>) -> Self::Params {
        BoxedMontyParams::new(modulus)
    }

    fn new(value: Self::Integer, params: Self::Params) -> Self {
        BoxedMontyForm::new(value, params)
    }

    fn zero(params: Self::Params) -> Self {
        BoxedMontyForm::zero(params)
    }

    fn one(params: Self::Params) -> Self {
        BoxedMontyForm::one(params)
    }
}

/// Convert the given integer into the Montgomery domain.
#[inline]
fn convert_to_montgomery(integer: &mut BoxedUint, params: &BoxedMontyParams) {
    let mut product = integer.mul(&params.r2);
    montgomery_reduction_boxed_mut(&mut product, &params.modulus, params.mod_neg_inv, integer);

    #[cfg(feature = "zeroize")]
    product.zeroize();
}

#[cfg(test)]
mod tests {
    use super::{BoxedMontyForm, BoxedMontyParams, BoxedUint};

    #[test]
    fn new_params_with_invalid_modulus() {
        // 0
        let ret = BoxedMontyParams::new(BoxedUint::zero());
        assert!(bool::from(ret.is_none()));

        // 2
        let ret = BoxedMontyParams::new(BoxedUint::from(2u8));
        assert!(bool::from(ret.is_none()));
    }

    #[test]
    fn new_params_with_valid_modulus() {
        BoxedMontyParams::new(BoxedUint::from(3u8)).unwrap();
    }

    #[test]
    fn div_by_2() {
        let params = BoxedMontyParams::new(BoxedUint::from(9u8)).unwrap();
        let zero = BoxedMontyForm::zero(params.clone());
        let one = BoxedMontyForm::one(params.clone());
        let two = one.add(&one);

        assert_eq!(zero.div_by_2(), zero);
        assert_eq!(one.div_by_2().mul(&two), one);
    }
}
