use crate::{CtChoice, Limb, Uint, WideWord, Word};

/// Algorithm 14.32 in Handbook of Applied Cryptography <https://cacr.uwaterloo.ca/hac/about/chap14.pdf>
pub const fn montgomery_reduction<const LIMBS: usize>(
    lower_upper: &(Uint<LIMBS>, Uint<LIMBS>),
    modulus: &Uint<LIMBS>,
    mod_neg_inv: Limb,
) -> Uint<LIMBS> {
    let (mut lower, mut upper) = *lower_upper;

    let mut meta_carry: WideWord = 0;

    let mut i = 0;
    while i < LIMBS {
        let u = (lower.limbs[i].0.wrapping_mul(mod_neg_inv.0)) as WideWord;

        let new_limb =
            (u * modulus.limbs[0].0 as WideWord).wrapping_add(lower.limbs[i].0 as WideWord);
        let mut carry = new_limb >> Word::BITS;

        let mut j = 1;
        while j < (LIMBS - i) {
            let new_limb = (u * modulus.limbs[j].0 as WideWord)
                .wrapping_add(lower.limbs[i + j].0 as WideWord)
                .wrapping_add(carry);
            carry = new_limb >> Word::BITS;
            lower.limbs[i + j] = Limb(new_limb as Word);

            j += 1;
        }
        while j < LIMBS {
            let new_limb = (u * modulus.limbs[j].0 as WideWord)
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
    let must_reduce = CtChoice::from_lsb(meta_carry as Word).or(Uint::ct_gt(modulus, &upper).not());
    upper = upper.wrapping_sub(&Uint::ct_select(&Uint::ZERO, modulus, must_reduce));

    upper
}
