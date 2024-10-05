//! Implements `MontyForm`s, supporting modular arithmetic with a modulus set at runtime.

mod add;
pub(super) mod inv;
mod lincomb;
mod mul;
mod neg;
mod pow;
mod sub;

use super::{
    const_monty_form::{ConstMontyForm, ConstMontyParams},
    div_by_2::div_by_2,
    reduction::montgomery_reduction,
    Retrieve,
};
use crate::{Concat, Limb, Monty, NonZero, Odd, Split, Uint, Word};
use subtle::{Choice, ConditionallySelectable, ConstantTimeEq};

/// Parameters to efficiently go to/from the Montgomery form for an odd modulus provided at runtime.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct MontyParams<const LIMBS: usize> {
    /// The constant modulus
    modulus: Odd<Uint<LIMBS>>,
    /// 1 in Montgomery form (a.k.a. `R`)
    one: Uint<LIMBS>,
    /// `R^2 mod modulus`, used to move into Montgomery form
    r2: Uint<LIMBS>,
    /// `R^3 mod modulus`, used to compute the multiplicative inverse
    r3: Uint<LIMBS>,
    /// The lowest limbs of -(MODULUS^-1) mod R
    /// We only need the LSB because during reduction this value is multiplied modulo 2**Limb::BITS.
    mod_neg_inv: Limb,
    /// Leading zeros in the modulus, used to choose optimized algorithms
    mod_leading_zeros: u32,
}

impl<const LIMBS: usize, const WIDE_LIMBS: usize> MontyParams<LIMBS>
where
    Uint<LIMBS>: Concat<Output = Uint<WIDE_LIMBS>>,
    Uint<WIDE_LIMBS>: Split<Output = Uint<LIMBS>>,
{
    /// Instantiates a new set of `MontyParams` representing the given odd `modulus`.
    pub fn new(modulus: Odd<Uint<LIMBS>>) -> Self {
        // `R mod modulus` where `R = 2^BITS`.
        // Represents 1 in Montgomery form.
        let one = Uint::MAX.rem(modulus.as_nz_ref()).wrapping_add(&Uint::ONE);

        // `R^2 mod modulus`, used to convert integers to Montgomery form.
        let r2 = one
            .square()
            .rem(&NonZero(modulus.0.concat(&Uint::ZERO)))
            .split()
            .0;

        // The modular inverse should always exist, because it was ensured odd above, which also ensures it's non-zero
        let inv_mod = modulus
            .inv_mod2k(Word::BITS)
            .expect("modular inverse should exist");

        let mod_neg_inv = Limb(Word::MIN.wrapping_sub(inv_mod.limbs[0].0));

        let mod_leading_zeros = modulus.as_ref().leading_zeros().max(Word::BITS - 1);

        // `R^3 mod modulus`, used for inversion in Montgomery form.
        let r3 = montgomery_reduction(&r2.square_wide(), &modulus, mod_neg_inv);

        Self {
            modulus,
            one,
            r2,
            r3,
            mod_neg_inv,
            mod_leading_zeros,
        }
    }
}

impl<const LIMBS: usize> MontyParams<LIMBS> {
    /// Instantiates a new set of `MontyParams` representing the given odd `modulus`.
    pub fn new_vartime(modulus: Odd<Uint<LIMBS>>) -> Self {
        // `R mod modulus` where `R = 2^BITS`.
        // Represents 1 in Montgomery form.
        let one = Uint::MAX
            .rem_vartime(modulus.as_nz_ref())
            .wrapping_add(&Uint::ONE);

        // `R^2 mod modulus`, used to convert integers to Montgomery form.
        let r2 = Uint::rem_wide_vartime(one.square_wide(), modulus.as_nz_ref());

        // The modular inverse should always exist, because it was ensured odd above, which also ensures it's non-zero
        let inv_mod = modulus
            .inv_mod2k_vartime(Word::BITS)
            .expect("modular inverse should exist");

        let mod_neg_inv = Limb(Word::MIN.wrapping_sub(inv_mod.limbs[0].0));

        let mod_leading_zeros = modulus.as_ref().leading_zeros().max(Word::BITS - 1);

        // `R^3 mod modulus`, used for inversion in Montgomery form.
        let r3 = montgomery_reduction(&r2.square_wide(), &modulus, mod_neg_inv);

        Self {
            modulus,
            one,
            r2,
            r3,
            mod_neg_inv,
            mod_leading_zeros,
        }
    }

    /// Returns the modulus which was used to initialize these parameters.
    pub const fn modulus(&self) -> &Odd<Uint<LIMBS>> {
        &self.modulus
    }

    /// Create `MontyParams` corresponding to a `ConstMontyParams`.
    pub const fn from_const_params<P>() -> Self
    where
        P: ConstMontyParams<LIMBS>,
    {
        Self {
            modulus: Odd(P::MODULUS.0),
            one: P::ONE,
            r2: P::R2,
            r3: P::R3,
            mod_neg_inv: P::MOD_NEG_INV,
            mod_leading_zeros: P::MOD_LEADING_ZEROS,
        }
    }
}

impl<const LIMBS: usize> ConditionallySelectable for MontyParams<LIMBS> {
    fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
        Self {
            modulus: Odd::conditional_select(&a.modulus, &b.modulus, choice),
            one: Uint::conditional_select(&a.one, &b.one, choice),
            r2: Uint::conditional_select(&a.r2, &b.r2, choice),
            r3: Uint::conditional_select(&a.r3, &b.r3, choice),
            mod_neg_inv: Limb::conditional_select(&a.mod_neg_inv, &b.mod_neg_inv, choice),
            mod_leading_zeros: u32::conditional_select(
                &a.mod_leading_zeros,
                &b.mod_leading_zeros,
                choice,
            ),
        }
    }
}

impl<const LIMBS: usize> ConstantTimeEq for MontyParams<LIMBS> {
    fn ct_eq(&self, other: &Self) -> Choice {
        self.modulus.ct_eq(&other.modulus)
            & self.one.ct_eq(&other.one)
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
    params: MontyParams<LIMBS>,
}

impl<const LIMBS: usize> MontyForm<LIMBS> {
    /// Instantiates a new `MontyForm` that represents this `integer` mod `MOD`.
    pub const fn new(integer: &Uint<LIMBS>, params: MontyParams<LIMBS>) -> Self {
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
    pub const fn zero(params: MontyParams<LIMBS>) -> Self {
        Self {
            montgomery_form: Uint::<LIMBS>::ZERO,
            params,
        }
    }

    /// Instantiates a new `MontyForm` that represents 1.
    pub const fn one(params: MontyParams<LIMBS>) -> Self {
        Self {
            montgomery_form: params.one,
            params,
        }
    }

    /// Returns the parameter struct used to initialize this object.
    pub const fn params(&self) -> &MontyParams<LIMBS> {
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
    pub const fn from_montgomery(integer: Uint<LIMBS>, params: MontyParams<LIMBS>) -> Self {
        Self {
            montgomery_form: integer,
            params,
        }
    }

    /// Extract the value from the `MontyForm` in Montgomery form.
    pub const fn to_montgomery(&self) -> Uint<LIMBS> {
        self.montgomery_form
    }

    /// Performs division by 2, that is returns `x` such that `x + x = self`.
    pub const fn div_by_2(&self) -> Self {
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

impl<const LIMBS: usize> Monty for MontyForm<LIMBS> {
    type Integer = Uint<LIMBS>;
    type Params = MontyParams<LIMBS>;

    fn new_params_vartime(modulus: Odd<Self::Integer>) -> Self::Params {
        MontyParams::new_vartime(modulus)
    }

    fn new(value: Self::Integer, params: Self::Params) -> Self {
        MontyForm::new(&value, params)
    }

    fn zero(params: Self::Params) -> Self {
        MontyForm::zero(params)
    }

    fn one(params: Self::Params) -> Self {
        MontyForm::one(params)
    }

    fn params(&self) -> &Self::Params {
        &self.params
    }

    fn as_montgomery(&self) -> &Self::Integer {
        &self.montgomery_form
    }

    fn double(&self) -> Self {
        MontyForm::double(self)
    }

    fn div_by_2(&self) -> Self {
        MontyForm::div_by_2(self)
    }

    fn lincomb_vartime(products: &[(&Self, &Self)]) -> Self {
        MontyForm::lincomb_vartime(products)
    }
}

impl<const LIMBS: usize, P: ConstMontyParams<LIMBS>> From<&ConstMontyForm<P, LIMBS>>
    for MontyForm<LIMBS>
{
    fn from(const_monty_form: &ConstMontyForm<P, LIMBS>) -> Self {
        Self {
            montgomery_form: const_monty_form.to_montgomery(),
            params: MontyParams::from_const_params::<P>(),
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
            params: MontyParams::conditional_select(&a.params, &b.params, choice),
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
