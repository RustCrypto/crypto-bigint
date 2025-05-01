//! Modular reduction implementation.

use crate::{Limb, Odd, Uint};

/// Algorithm 14.32 in Handbook of Applied Cryptography <https://cacr.uwaterloo.ca/hac/about/chap14.pdf>
#[inline(always)]
const fn montgomery_reduction_inner(
    upper: &mut [Limb],
    lower: &mut [Limb],
    modulus: &[Limb],
    mod_neg_inv: Limb,
) -> Limb {
    let nlimbs = modulus.len();
    debug_assert!(nlimbs == upper.len());
    debug_assert!(nlimbs == lower.len());

    let mut meta_carry = Limb::ZERO;
    let mut new_sum;

    let mut i = 0;
    while i < nlimbs {
        let u = lower[i].wrapping_mul(mod_neg_inv);

        let (_, mut carry) = lower[i].carrying_mul_add(u, modulus[0], Limb::ZERO);
        let mut new_limb;

        let mut j = 1;
        while j < (nlimbs - i) {
            (new_limb, carry) = lower[i + j].carrying_mul_add(u, modulus[j], carry);
            lower[i + j] = new_limb;
            j += 1;
        }
        while j < nlimbs {
            (new_limb, carry) = upper[i + j - nlimbs].carrying_mul_add(u, modulus[j], carry);
            upper[i + j - nlimbs] = new_limb;
            j += 1;
        }

        (new_sum, meta_carry) = upper[i].carrying_add(carry, meta_carry);
        upper[i] = new_sum;

        i += 1;
    }

    meta_carry
}

/// Algorithm 14.32 in Handbook of Applied Cryptography <https://cacr.uwaterloo.ca/hac/about/chap14.pdf>
pub const fn montgomery_reduction<const LIMBS: usize>(
    lower_upper: &(Uint<LIMBS>, Uint<LIMBS>),
    modulus: &Odd<Uint<LIMBS>>,
    mod_neg_inv: Limb,
) -> Uint<LIMBS> {
    let (mut lower, mut upper) = *lower_upper;
    let meta_carry = montgomery_reduction_inner(
        &mut upper.limbs,
        &mut lower.limbs,
        &modulus.0.limbs,
        mod_neg_inv,
    );

    // Division is simply taking the upper half of the limbs
    // Final reduction (at this point, the value is at most 2 * modulus,
    // so `meta_carry` is either 0 or 1)
    upper.sub_mod_with_carry(meta_carry, &modulus.0, &modulus.0)
}
