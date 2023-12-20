//! Implements `MontyForm`s, supporting modular arithmetic with a modulus set at runtime.

mod add;
pub(super) mod inv;
mod mul;
mod neg;
mod pow;
mod sub;

use super::{
    const_monty_form::{ConstMontyForm, ConstMontyFormParams},
    div_by_2::div_by_2,
    reduction::montgomery_reduction,
    Retrieve,
};
use crate::{Limb, NonZero, Uint, Word, Zero};
use subtle::{Choice, ConditionallySelectable, ConstantTimeEq, CtOption};

/// Parameters to efficiently go to/from the Montgomery form for an odd modulus provided at runtime.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct MontyFormParams<const LIMBS: usize> {
    /// The constant modulus
    modulus: Uint<LIMBS>,
    /// Parameter used in Montgomery reduction
    r: Uint<LIMBS>,
    /// R^2, used to move into Montgomery form
    r2: Uint<LIMBS>,
    /// R^3, used to compute the multiplicative inverse
    r3: Uint<LIMBS>,
    /// The lowest limbs of -(MODULUS^-1) mod R
    /// We only need the LSB because during reduction this value is multiplied modulo 2**Limb::BITS.
    mod_neg_inv: Limb,
}

impl<const LIMBS: usize> MontyFormParams<LIMBS> {
    /// Instantiates a new set of `MontyFormParams` representing the given `modulus` if it is odd.
    ///
    /// Returns `None` if the provided modulus is not odd.
    pub fn new(modulus: &Uint<LIMBS>) -> CtOption<Self> {
        // Use a surrogate value of `1` in case a modulus of `0` is passed.
        // This will be rejected by the `modulus_is_odd` check below,
        // which will fail and return `None`.
        let nz_modulus = NonZero::new(Uint::conditional_select(
            modulus,
            &Uint::ONE,
            modulus.is_zero(),
        ))
        .expect("modulus ensured non-zero");

        let r = Uint::MAX.rem_vartime(&nz_modulus).wrapping_add(&Uint::ONE);
        let r2 = Uint::rem_wide_vartime(r.square_wide(), &nz_modulus);

        let maybe_inverse = modulus.inv_mod2k_vartime(Word::BITS);
        // If the inverse exists, it means the modulus is odd.
        let (inv_mod_limb, modulus_is_odd) = maybe_inverse.components_ref();
        let mod_neg_inv = Limb(Word::MIN.wrapping_sub(inv_mod_limb.limbs[0].0));

        let r3 = montgomery_reduction(&r2.square_wide(), modulus, mod_neg_inv);

        let params = Self {
            modulus: *modulus,
            r,
            r2,
            r3,
            mod_neg_inv,
        };

        CtOption::new(params, modulus_is_odd.into())
    }

    /// Returns the modulus which was used to initialize these parameters.
    pub const fn modulus(&self) -> &Uint<LIMBS> {
        &self.modulus
    }

    /// Create `MontyFormParams` corresponding to a `ConstMontyFormParams`.
    pub const fn from_const_params<P>() -> Self
    where
        P: ConstMontyFormParams<LIMBS>,
    {
        Self {
            modulus: P::MODULUS.0,
            r: P::R,
            r2: P::R2,
            r3: P::R3,
            mod_neg_inv: P::MOD_NEG_INV,
        }
    }
}

impl<const LIMBS: usize> ConditionallySelectable for MontyFormParams<LIMBS> {
    fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
        Self {
            modulus: Uint::conditional_select(&a.modulus, &b.modulus, choice),
            r: Uint::conditional_select(&a.r, &b.r, choice),
            r2: Uint::conditional_select(&a.r2, &b.r2, choice),
            r3: Uint::conditional_select(&a.r3, &b.r3, choice),
            mod_neg_inv: Limb::conditional_select(&a.mod_neg_inv, &b.mod_neg_inv, choice),
        }
    }
}

impl<const LIMBS: usize> ConstantTimeEq for MontyFormParams<LIMBS> {
    fn ct_eq(&self, other: &Self) -> Choice {
        self.modulus.ct_eq(&other.modulus)
            & self.r.ct_eq(&other.r)
            & self.r2.ct_eq(&other.r2)
            & self.r3.ct_eq(&other.r3)
            & self.mod_neg_inv.ct_eq(&other.mod_neg_inv)
    }
}

/// An integer in Montgomery form represented using `LIMBS` limbs.
/// The odd modulus is set at runtime.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct MontyForm<const LIMBS: usize> {
    montgomery_form: Uint<LIMBS>,
    params: MontyFormParams<LIMBS>,
}

impl<const LIMBS: usize> MontyForm<LIMBS> {
    /// Instantiates a new `MontyForm` that represents this `integer` mod `MOD`.
    pub const fn new(integer: &Uint<LIMBS>, params: MontyFormParams<LIMBS>) -> Self {
        let product = integer.split_mul(&params.r2);
        let montgomery_form = montgomery_reduction(&product, &params.modulus, params.mod_neg_inv);

        Self {
            montgomery_form,
            params,
        }
    }

    /// Retrieves the integer currently encoded in this `MontyForm`, guaranteed to be reduced.
    pub const fn retrieve(&self) -> Uint<LIMBS> {
        montgomery_reduction(
            &(self.montgomery_form, Uint::ZERO),
            &self.params.modulus,
            self.params.mod_neg_inv,
        )
    }

    /// Instantiates a new `MontyForm` that represents zero.
    pub const fn zero(params: MontyFormParams<LIMBS>) -> Self {
        Self {
            montgomery_form: Uint::<LIMBS>::ZERO,
            params,
        }
    }

    /// Instantiates a new `MontyForm` that represents 1.
    pub const fn one(params: MontyFormParams<LIMBS>) -> Self {
        Self {
            montgomery_form: params.r,
            params,
        }
    }

    /// Returns the parameter struct used to initialize this object.
    pub const fn params(&self) -> &MontyFormParams<LIMBS> {
        &self.params
    }

    /// Access the `MontyForm` value in Montgomery form.
    pub const fn as_montgomery(&self) -> &Uint<LIMBS> {
        &self.montgomery_form
    }

    /// Mutably access the `MontyForm` value in Montgomery form.
    pub fn as_montgomery_mut(&mut self) -> &mut Uint<LIMBS> {
        &mut self.montgomery_form
    }

    /// Create a `MontyForm` from a value in Montgomery form.
    pub const fn from_montgomery(integer: Uint<LIMBS>, params: MontyFormParams<LIMBS>) -> Self {
        Self {
            montgomery_form: integer,
            params,
        }
    }

    /// Extract the value from the `MontyForm` in Montgomery form.
    pub const fn to_montgomery(&self) -> Uint<LIMBS> {
        self.montgomery_form
    }

    /// Performs the modular division by 2, that is for given `x` returns `y`
    /// such that `y * 2 = x mod p`. This means:
    /// - if `x` is even, returns `x / 2`,
    /// - if `x` is odd, returns `(x + p) / 2`
    ///   (since the modulus `p` in Montgomery form is always odd, this divides entirely).
    pub fn div_by_2(&self) -> Self {
        Self {
            montgomery_form: div_by_2(&self.montgomery_form, &self.params.modulus),
            params: self.params,
        }
    }
}

impl<const LIMBS: usize> Retrieve for MontyForm<LIMBS> {
    type Output = Uint<LIMBS>;
    fn retrieve(&self) -> Self::Output {
        self.retrieve()
    }
}

impl<const LIMBS: usize, P: ConstMontyFormParams<LIMBS>> From<&ConstMontyForm<P, LIMBS>>
    for MontyForm<LIMBS>
{
    fn from(const_monty_form: &ConstMontyForm<P, LIMBS>) -> Self {
        Self {
            montgomery_form: const_monty_form.to_montgomery(),
            params: MontyFormParams::from_const_params::<P>(),
        }
    }
}

impl<const LIMBS: usize> ConditionallySelectable for MontyForm<LIMBS> {
    fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
        Self {
            montgomery_form: Uint::conditional_select(
                &a.montgomery_form,
                &b.montgomery_form,
                choice,
            ),
            params: MontyFormParams::conditional_select(&a.params, &b.params, choice),
        }
    }
}

impl<const LIMBS: usize> ConstantTimeEq for MontyForm<LIMBS> {
    fn ct_eq(&self, other: &Self) -> Choice {
        self.montgomery_form.ct_eq(&other.montgomery_form) & self.params.ct_eq(&other.params)
    }
}

/// NOTE: this does _not_ zeroize the parameters, in order to maintain some form of type consistency
#[cfg(feature = "zeroize")]
impl<const LIMBS: usize> zeroize::Zeroize for MontyForm<LIMBS> {
    fn zeroize(&mut self) {
        self.montgomery_form.zeroize()
    }
}

#[cfg(test)]
mod test {
    use super::*;

    const LIMBS: usize = nlimbs!(64);

    #[test]
    // Test that a valid modulus yields `MontyFormParams`
    fn test_valid_modulus() {
        let valid_modulus = Uint::<LIMBS>::from(3u8);
        MontyFormParams::<LIMBS>::new(&valid_modulus).unwrap();
    }

    #[test]
    // Test that an invalid checked modulus does not yield `MontyFormParams`
    fn test_invalid_checked_modulus() {
        assert!(bool::from(
            MontyFormParams::<LIMBS>::new(&Uint::from(2u8)).is_none()
        ))
    }
}
