use core::marker::PhantomData;

use subtle::{Choice, ConditionallySelectable};

use crate::{Limb, UInt, WideWord, Word};

#[macro_use]
/// Macros to remove the boilerplate code when dealing with constant moduli.
pub mod macros;
/// Additions between residues
mod add;
/// Multiplications between residues
mod mul;
/// Exponentiation of residues
mod pow;

/// The parameters to efficiently go to and from the Montgomery form for a given modulus. An easy way to generate these parameters is using the `impl_modulus!` macro.
///
/// Unfortunately, `LIMBS` must be generic for now until const generics are stabilized.
pub trait ResidueParams<const LIMBS: usize>: Copy {
    /// Number of limbs required to encode a residue
    const LIMBS: usize;

    /// The constant modulus
    const MODULUS: UInt<LIMBS>;
    /// Parameter used in Montgomery reduction
    const R: UInt<LIMBS>;
    /// R^2, used to move into Montgomery form
    const R2: UInt<LIMBS>;
    /// The lowest limbs of -(MODULUS^-1) mod R
    // We only need the LSB because during reduction this value is multiplied modulo 2**64.
    const MOD_NEG_INV: Limb;
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
/// A residue mod `MOD`, represented using `LIMBS` limbs.
pub struct Residue<MOD, const LIMBS: usize>
where
    MOD: ResidueParams<LIMBS>,
{
    montgomery_form: UInt<LIMBS>,
    phantom: PhantomData<MOD>,
}

impl<MOD: ResidueParams<LIMBS>, const LIMBS: usize> Residue<MOD, LIMBS> {
    /// The representation of 1 mod `MOD`.
    pub const ONE: Self = Self {
        montgomery_form: MOD::R,
        phantom: PhantomData,
    };

    /// Instantiates a new `Residue` that represents this `integer` mod `MOD`.
    pub const fn new(integer: UInt<LIMBS>) -> Self {
        let mut modular_integer = Residue {
            montgomery_form: integer,
            phantom: PhantomData,
        };

        let product = integer.mul_wide(&MOD::R2);
        modular_integer.montgomery_form = montgomery_reduction::<MOD, LIMBS>(product);

        modular_integer
    }

    /// Retrieves the `integer` currently encoded in this `Residue`, guaranteed to be reduced.
    pub const fn retrieve(&self) -> UInt<LIMBS> {
        montgomery_reduction::<MOD, LIMBS>((self.montgomery_form, UInt::ZERO))
    }

    /// Return `a` if `c`==0 or `b` if `c`==`Word::MAX`.
    ///
    /// Const-friendly: we can't yet use `subtle` in `const fn` contexts.
    #[inline]
    pub(crate) const fn ct_select(a: Self, b: Self, c: Word) -> Self {
        Residue {
            montgomery_form: UInt::ct_select(a.montgomery_form, b.montgomery_form, c),
            phantom: PhantomData,
        }
    }
}

/// Algorithm 14.32 in Handbook of Applied Cryptography (https://cacr.uwaterloo.ca/hac/about/chap14.pdf)
const fn montgomery_reduction<MOD: ResidueParams<LIMBS>, const LIMBS: usize>(
    lower_upper: (UInt<LIMBS>, UInt<LIMBS>),
) -> UInt<LIMBS> {
    let (mut lower, mut upper) = lower_upper;

    let mut meta_carry = 0;

    let mut i = 0;
    while i < LIMBS {
        let u = (lower.limbs[i].0.wrapping_mul(MOD::MOD_NEG_INV.0)) as WideWord;

        let new_limb =
            (u * MOD::MODULUS.limbs[0].0 as WideWord).wrapping_add(lower.limbs[i].0 as WideWord);
        let mut carry = new_limb >> Word::BITS;

        let mut j = 1;
        while j < (LIMBS - i) {
            let new_limb = (u * MOD::MODULUS.limbs[j].0 as WideWord)
                .wrapping_add(lower.limbs[i + j].0 as WideWord)
                .wrapping_add(carry);
            carry = new_limb >> Word::BITS;
            lower.limbs[i + j] = Limb(new_limb as Word);

            j += 1;
        }
        while j < LIMBS {
            let new_limb = (u * MOD::MODULUS.limbs[j].0 as WideWord)
                .wrapping_add(upper.limbs[i + j - LIMBS].0 as WideWord)
                .wrapping_add(carry);
            carry = new_limb >> Word::BITS;
            upper.limbs[i + j - LIMBS] = Limb(new_limb as Word);

            j += 1;
        }

        let new_sum = (upper.limbs[i].0 as WideWord)
            .wrapping_add(carry)
            .wrapping_add(meta_carry);
        meta_carry = new_sum >> Word::BITS;
        upper.limbs[i] = Limb(new_sum as Word);

        i += 1;
    }

    // Division is simply taking the upper half of the limbs
    // Final reduction (at this point, the value is at most 2 * modulus)
    let must_reduce = (meta_carry as Word).saturating_mul(Word::MAX)
        | ((upper.ct_cmp(&MOD::MODULUS) != -1) as Word).saturating_mul(Word::MAX);
    upper = upper.wrapping_sub(&UInt::ct_select(UInt::ZERO, MOD::MODULUS, must_reduce));

    upper
}

impl<MOD: ResidueParams<LIMBS> + Copy, const LIMBS: usize> ConditionallySelectable
    for Residue<MOD, LIMBS>
{
    fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
        Residue {
            montgomery_form: UInt::conditional_select(
                &a.montgomery_form,
                &b.montgomery_form,
                choice,
            ),
            phantom: PhantomData,
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        traits::Encoding,
        uint::modular::{montgomery_reduction, Residue, ResidueParams},
        UInt, U256, U64,
    };

    impl_modulus!(
        Modulus1,
        U256,
        "73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001"
    );

    #[test]
    fn test_montgomery_params() {
        assert_eq!(
            Modulus1::R,
            U256::from_be_hex("1824b159acc5056f998c4fefecbc4ff55884b7fa0003480200000001fffffffe")
        );
        assert_eq!(
            Modulus1::R2,
            U256::from_be_hex("0748d9d99f59ff1105d314967254398f2b6cedcb87925c23c999e990f3f29c6d")
        );
        assert_eq!(
            Modulus1::MOD_NEG_INV,
            U64::from_be_hex("fffffffeffffffff").limbs[0]
        );
    }

    impl_modulus!(
        Modulus2,
        U256,
        "ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551"
    );

    #[test]
    fn test_reducing_r() {
        // Divide the value R by R, which should equal 1
        assert_eq!(
            montgomery_reduction::<Modulus2, { Modulus2::LIMBS }>((Modulus2::R, UInt::ZERO)),
            UInt::ONE
        );
    }

    #[test]
    fn test_reducing_r2() {
        // Divide the value R^2 by R, which should equal R
        assert_eq!(
            montgomery_reduction::<Modulus2, { Modulus2::LIMBS }>((Modulus2::R2, UInt::ZERO)),
            Modulus2::R
        );
    }

    #[test]
    fn test_reducing_r2_wide() {
        // Divide the value R^2 by R, which should equal R
        let (hi, lo) = Modulus2::R.square().split();
        assert_eq!(
            montgomery_reduction::<Modulus2, { Modulus2::LIMBS }>((lo, hi)),
            Modulus2::R
        );
    }

    #[test]
    fn test_reducing_xr_wide() {
        // Reducing xR should return x
        let x =
            U256::from_be_hex("44acf6b7e36c1342c2c5897204fe09504e1e2efb1a900377dbc4e7a6a133ec56");
        let product = x.mul_wide(&Modulus2::R);
        assert_eq!(
            montgomery_reduction::<Modulus2, { Modulus2::LIMBS }>(product),
            x
        );
    }

    #[test]
    fn test_reducing_xr2_wide() {
        // Reducing xR^2 should return xR
        let x =
            U256::from_be_hex("44acf6b7e36c1342c2c5897204fe09504e1e2efb1a900377dbc4e7a6a133ec56");
        let product = x.mul_wide(&Modulus2::R2);

        // Computing xR mod modulus without Montgomery reduction
        let (lo, hi) = x.mul_wide(&Modulus2::R);
        let c = hi.concat(&lo);
        let red = c.reduce(&U256::ZERO.concat(&Modulus2::MODULUS)).unwrap();
        let (hi, lo) = red.split();
        assert_eq!(hi, UInt::ZERO);

        assert_eq!(
            montgomery_reduction::<Modulus2, { Modulus2::LIMBS }>(product),
            lo
        );
    }

    #[test]
    fn test_new_retrieve() {
        let x =
            U256::from_be_hex("44acf6b7e36c1342c2c5897204fe09504e1e2efb1a900377dbc4e7a6a133ec56");
        let x_mod = Residue::<Modulus2, { Modulus2::LIMBS }>::new(x);

        // Confirm that when creating a Modular and retrieving the value, that it equals the original
        assert_eq!(x, x_mod.retrieve());
    }

    #[test]
    fn test_residue_macro() {
        let x =
            U256::from_be_hex("44acf6b7e36c1342c2c5897204fe09504e1e2efb1a900377dbc4e7a6a133ec56");
        assert_eq!(
            Residue::<Modulus2, { Modulus2::LIMBS }>::new(x),
            residue!(x, Modulus2)
        );
    }
}
