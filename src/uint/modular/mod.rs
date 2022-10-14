use core::marker::PhantomData;

use subtle::{Choice, ConditionallySelectable};

use crate::{CheckedAdd, Concat, Limb, Split, UInt, WideWord, Word, U256};

#[macro_use]
mod macros;

mod add;
mod mul;
mod pow;

pub trait ResidueParams<const LIMBS: usize>: Copy {
    const MODULUS: UInt<LIMBS>;
    const R: UInt<LIMBS>;
    const R2: UInt<LIMBS>;
    // We only need the LSB because during reduction this value is multiplied modulo 2**64.
    const MOD_NEG_INV: Limb;
}

// impl<const LIMBS: usize, const DLIMBS: usize> ResidueParams<LIMBS>
// where
//     UInt<LIMBS>: Concat<Output = UInt<DLIMBS>>,
//     UInt<DLIMBS>: Split<Output = UInt<LIMBS>>,
// {
//     /// Note that the modulus must be tight (i.e. it should be at least somewhat close in size to `LIMB_COUNT`).
//     pub fn new(modulus: UInt<LIMBS>) -> Self {
//         let montgomery_r = UInt::MAX
//             .reduce(&modulus)
//             .unwrap()
//             .checked_add(&UInt::ONE)
//             .unwrap();

//         let double_modulus = (UInt::<LIMBS>::ZERO).concat(&modulus);
//         let (_, montgomery_r2) = montgomery_r
//             .square()
//             .reduce(&double_modulus)
//             .unwrap()
//             .split();

//         let modulus_neg_inv =
//             Limb(Word::MIN.wrapping_sub(modulus.inv_mod2k(Word::BITS as usize).limbs[0].0));

//         ResidueParams {
//             modulus,
//             montgomery_r,
//             montgomery_r2,
//             modulus_neg_inv,
//         }
//     }
// }

// #[derive(Clone, Copy)]
// pub struct ThisModulus {}
// impl<const DLIMBS: usize> ResidueParams<4> for ThisModulus
// where
//     UInt<4>: Concat<Output = UInt<DLIMBS>>,
//     UInt<DLIMBS>: Split<Output = UInt<4>>,
// {
//     const MODULUS: UInt<4> = UInt::<4>::from_be_hex("73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001");
//     const R: UInt<4> = compute_montgomery_r(Self::MODULUS);
//     const R2: UInt<4> = compute_montgomery_r2(Self::MODULUS, Self::R);
//     const MOD_NEG_INV: Limb = compute_montgomery_mod_neg_inv(Self::MODULUS);
// }

// TODO: We should consider taking modulus_params as a reference
#[derive(Debug, Clone, Copy)]
pub struct Residue<MOD, const LIMBS: usize>
where MOD: ResidueParams<LIMBS>
{
    montgomery_form: UInt<LIMBS>,
    phantom: PhantomData<MOD>,
}

impl<MOD: ResidueParams<LIMBS>, const LIMBS: usize> Residue<MOD, LIMBS> {
    pub const ONE: Self = Self {
        montgomery_form: MOD::R,
        phantom: PhantomData,
    };

    pub fn new(integer: UInt<LIMBS>) -> Self {
        let mut modular_integer = Residue {
            montgomery_form: integer,
            phantom: PhantomData
        };

        let product = integer.mul_wide(&MOD::R2);
        modular_integer.montgomery_form = montgomery_reduction::<MOD, LIMBS>(product);

        modular_integer
    }

    pub fn retrieve(&self) -> UInt<LIMBS> {
        montgomery_reduction::<MOD, LIMBS>((self.montgomery_form, UInt::ZERO))
    }

    /// Return `a` if `c`==0 or `b` if `c`==`Word::MAX`.
    ///
    /// Const-friendly: we can't yet use `subtle` in `const fn` contexts.
    #[inline]
    pub(crate) const fn ct_select(a: Self, b: Self, c: Word) -> Self {
        Residue {
            montgomery_form: UInt::ct_select(a.montgomery_form, b.montgomery_form, c),
            phantom: PhantomData
        }
    }
}

/// Algorithm 14.32 in Handbook of Applied Cryptography (https://cacr.uwaterloo.ca/hac/about/chap14.pdf)
fn montgomery_reduction<MOD: ResidueParams<LIMBS>, const LIMBS: usize>(
    lower_upper: (UInt<LIMBS>, UInt<LIMBS>),
) -> UInt<LIMBS> {
    let (mut lower, mut upper) = lower_upper;

    let mut meta_carry = 0;

    let mut i = 0;
    while i < LIMBS {
        let u = (lower.limbs[i]
            .0
            .wrapping_mul(MOD::MOD_NEG_INV.0)) as WideWord;

        let new_limb = (u * MOD::MODULUS.limbs[0].0 as WideWord)
            .wrapping_add(lower.limbs[i].0 as WideWord);
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
    let must_reduce =
        Choice::from(meta_carry as u8) | Choice::from((upper >= MOD::MODULUS) as u8);
    upper = upper.wrapping_sub(&UInt::conditional_select(
        &UInt::ZERO,
        &MOD::MODULUS,
        must_reduce,
    ));

    upper
}

impl<MOD: ResidueParams<LIMBS> + Copy, const LIMBS: usize> ConditionallySelectable for Residue<MOD, LIMBS> {
    fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
        Residue {
            montgomery_form: UInt::conditional_select(&a.montgomery_form, &b.montgomery_form, choice),
            phantom: PhantomData,
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        uint::modular::{montgomery_reduction, Residue, ResidueParams},
        UInt, U256, U64,
    };

    impl_modulus!(ThisModulus, U256, "73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001");

    #[test]
    fn test_montgomery_params() {
        assert_eq!(
            ThisModulus::R,
            U256::from_be_hex("1824b159acc5056f998c4fefecbc4ff55884b7fa0003480200000001fffffffe")
        );
        assert_eq!(
            ThisModulus::R2,
            U256::from_be_hex("0748d9d99f59ff1105d314967254398f2b6cedcb87925c23c999e990f3f29c6d")
        );
        assert_eq!(
            ThisModulus::MOD_NEG_INV,
            U64::from_be_hex("fffffffeffffffff").limbs[0]
        );
    }

    // #[test]
    // fn test_reducing_r() {
    //     let modulus =
    //         U256::from_be_hex("ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551");
    //     let modulus_params = ResidueParams::new(modulus);

    //     // Divide the value R by R, which should equal 1
    //     assert_eq!(
    //         montgomery_reduction((modulus_params.montgomery_r, UInt::ZERO)),
    //         UInt::ONE
    //     );
    // }

    // #[test]
    // fn test_reducing_r2() {
    //     let modulus =
    //         U256::from_be_hex("ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551");
    //     let modulus_params = ResidueParams::new(modulus);

    //     // Divide the value R^2 by R, which should equal R
    //     assert_eq!(
    //         montgomery_reduction((modulus_params.montgomery_r2, UInt::ZERO)),
    //         modulus_params.montgomery_r
    //     );
    // }

    // #[test]
    // fn test_reducing_r2_wide() {
    //     let modulus =
    //         U256::from_be_hex("ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551");
    //     let modulus_params = ResidueParams::new(modulus);

    //     // Divide the value R^2 by R, which should equal R
    //     let (hi, lo) = modulus_params.montgomery_r.square().split();
    //     assert_eq!(
    //         montgomery_reduction((lo, hi)),
    //         modulus_params.montgomery_r
    //     );
    // }

    // #[test]
    // fn test_reducing_xr_wide() {
    //     let modulus =
    //         U256::from_be_hex("ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551");
    //     let modulus_params = ResidueParams::new(modulus);

    //     // Reducing xR should return x
    //     let x =
    //         U256::from_be_hex("44acf6b7e36c1342c2c5897204fe09504e1e2efb1a900377dbc4e7a6a133ec56");
    //     let product = x.mul_wide(&modulus_params.montgomery_r);
    //     assert_eq!(montgomery_reduction(product), x);
    // }

    // #[test]
    // fn test_reducing_xr2_wide() {
    //     let modulus =
    //         U256::from_be_hex("ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551");
    //     let modulus_params = ResidueParams::new(modulus);

    //     // Reducing xR^2 should return xR
    //     let x =
    //         U256::from_be_hex("44acf6b7e36c1342c2c5897204fe09504e1e2efb1a900377dbc4e7a6a133ec56");
    //     let product = x.mul_wide(&modulus_params.montgomery_r2);

    //     // Computing xR mod modulus without Montgomery reduction
    //     let (lo, hi) = x.mul_wide(&modulus_params.montgomery_r);
    //     let c = hi.concat(&lo);
    //     let red = c.reduce(&U256::ZERO.concat(&modulus)).unwrap();
    //     let (hi, lo) = red.split();
    //     assert_eq!(hi, UInt::ZERO);

    //     assert_eq!(montgomery_reduction(product), lo);
    // }

    // #[test]
    // fn test_new_retrieve() {
    //     let modulus =
    //         U256::from_be_hex("ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551");

    //     //let modulus = U256::new([Limb(0xffffffff00000001), Limb(0x53bda402fffe5bfe), Limb(0x3339d80809a1d805), Limb(0x73eda753299d7d48)]);
    //     let modulus_params = ResidueParams::new(modulus);

    //     let x =
    //         U256::from_be_hex("44acf6b7e36c1342c2c5897204fe09504e1e2efb1a900377dbc4e7a6a133ec56");
    //     let x_mod = Residue::new(x);

    //     // Confirm that when creating a Modular and retrieving the value, that it equals the original
    //     assert_eq!(x, x_mod.retrieve());
    // }
}
