use crate::{Limb, Uint, WideWord, Word};

/// Returns `(hi, lo)` such that `hi * R + lo = x * y + z + w`.
#[inline(always)]
const fn muladdcarry(x: Word, y: Word, z: Word, w: Word) -> (Word, Word) {
    let res = (x as WideWord)
        .wrapping_mul(y as WideWord)
        .wrapping_add(z as WideWord)
        .wrapping_add(w as WideWord);
    ((res >> Word::BITS) as Word, res as Word)
}

/// Impl the core Montgomery reduction algorithm.
///
/// This is implemented as a macro to abstract over `const fn` and boxed use cases, since the latter
/// needs mutable references and thus the unstable `const_mut_refs` feature (rust-lang/rust#57349).
// TODO(tarcieri): change this into a `const fn` when `const_mut_refs` is stable
macro_rules! impl_montgomery_reduction {
    ($upper:expr, $lower:expr, $modulus:expr, $mod_neg_inv:expr, $limbs:expr) => {{
        let mut meta_carry = Limb(0);
        let mut new_sum;

        let mut i = 0;
        while i < $limbs {
            let u = $lower[i].0.wrapping_mul($mod_neg_inv.0);

            let (mut carry, _) = muladdcarry(u, $modulus[0].0, $lower[i].0, 0);
            let mut new_limb;

            let mut j = 1;
            while j < ($limbs - i) {
                (carry, new_limb) = muladdcarry(u, $modulus[j].0, $lower[i + j].0, carry);
                $lower[i + j] = Limb(new_limb);
                j += 1;
            }
            while j < $limbs {
                (carry, new_limb) = muladdcarry(u, $modulus[j].0, $upper[i + j - $limbs].0, carry);
                $upper[i + j - $limbs] = Limb(new_limb);
                j += 1;
            }

            (new_sum, meta_carry) = $upper[i].adc(Limb(carry), meta_carry);
            $upper[i] = new_sum;

            i += 1;
        }

        meta_carry
    }};
}

/// Algorithm 14.32 in Handbook of Applied Cryptography <https://cacr.uwaterloo.ca/hac/about/chap14.pdf>
pub const fn montgomery_reduction<const LIMBS: usize>(
    lower_upper: &(Uint<LIMBS>, Uint<LIMBS>),
    modulus: &Uint<LIMBS>,
    mod_neg_inv: Limb,
) -> Uint<LIMBS> {
    let (mut lower, mut upper) = *lower_upper;
    let meta_carry =
        impl_montgomery_reduction!(upper.limbs, lower.limbs, &modulus.limbs, mod_neg_inv, LIMBS);

    // Division is simply taking the upper half of the limbs
    // Final reduction (at this point, the value is at most 2 * modulus,
    // so `meta_carry` is either 0 or 1)
    upper.sub_mod_with_carry(meta_carry, modulus, modulus)
}

/// Shim used by [`BoxedUint`] to perform a Montgomery reduction.
#[cfg(feature = "alloc")]
pub(crate) fn montgomery_reduction_core(
    lower: &mut [Limb],
    upper: &mut [Limb],
    modulus: &[Limb],
    mod_neg_inv: Limb,
) -> Limb {
    debug_assert_eq!(lower.len(), modulus.len());
    debug_assert_eq!(upper.len(), modulus.len());
    impl_montgomery_reduction!(upper, lower, modulus, mod_neg_inv, modulus.len())
}
