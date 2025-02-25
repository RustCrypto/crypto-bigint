//! Modular reduction implementation.

use crate::{Limb, Odd, Uint};

#[cfg(feature = "alloc")]
use crate::BoxedUint;

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

        let (_, mut carry) = lower[i].mac(u, modulus[0], Limb::ZERO);
        let mut new_limb;

        let mut j = 1;
        while j < (nlimbs - i) {
            (new_limb, carry) = lower[i + j].mac(u, modulus[j], carry);
            lower[i + j] = new_limb;
            j += 1;
        }
        while j < nlimbs {
            (new_limb, carry) = upper[i + j - nlimbs].mac(u, modulus[j], carry);
            upper[i + j - nlimbs] = new_limb;
            j += 1;
        }

        (new_sum, meta_carry) = upper[i].adc(carry, meta_carry);
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

/// Algorithm 14.32 in Handbook of Applied Cryptography <https://cacr.uwaterloo.ca/hac/about/chap14.pdf>
///
/// This version writes the result into the provided [`BoxedUint`].
#[cfg(feature = "alloc")]
pub(crate) fn montgomery_reduction_boxed_mut(
    x: &mut BoxedUint,
    modulus: &BoxedUint,
    mod_neg_inv: Limb,
    out: &mut BoxedUint,
) {
    debug_assert_eq!(x.nlimbs(), modulus.nlimbs() * 2);
    debug_assert_eq!(out.nlimbs(), modulus.nlimbs());

    let (lower, upper) = x.limbs.split_at_mut(modulus.nlimbs());
    let meta_carry = montgomery_reduction_inner(upper, lower, &modulus.limbs, mod_neg_inv);

    // Division is simply taking the upper half of the limbs
    // Final reduction (at this point, the value is at most 2 * modulus,
    // so `meta_carry` is either 0 or 1)
    out.limbs.copy_from_slice(upper);
    out.sub_assign_mod_with_carry(meta_carry, modulus, modulus);
}

/// Algorithm 14.32 in Handbook of Applied Cryptography <https://cacr.uwaterloo.ca/hac/about/chap14.pdf>
///
/// This version allocates and returns a [`BoxedUint`].
#[cfg(feature = "alloc")]
#[inline]
pub(crate) fn montgomery_reduction_boxed(
    x: &mut BoxedUint,
    modulus: &BoxedUint,
    mod_neg_inv: Limb,
) -> BoxedUint {
    let mut ret = BoxedUint::zero_with_precision(modulus.bits_precision());
    montgomery_reduction_boxed_mut(x, modulus, mod_neg_inv, &mut ret);
    ret
}
