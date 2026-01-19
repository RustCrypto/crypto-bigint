use super::reduction::montgomery_reduction;
use crate::{Limb, Odd, Uint, WideWord, Word};

/// Based on Algorithm 14.36 in Handbook of Applied Cryptography
/// <https://cacr.uwaterloo.ca/hac/about/chap14.pdf>
///
/// Multiply `x` and `y` in Montgomery form, producing `x•y•R^-1 mod modulus + a•modulus`.
///
/// This algorithm roughly corresponds to the Finely Integrated Operand Scanning (FIOS)
/// method of "Analyzing and Comparing Montgomery Multiplication Algorithms" by Koc et al
/// <https://www.microsoft.com/en-us/research/wp-content/uploads/1996/01/j37acmon.pdf>
/// but using wide words to track the intermediate products and carry.
///
/// The final conditional subtraction of the modulus to produce a result in the range
/// `[0, modulus)` is not performed here, and must be performed by the caller. In some
/// cases this may be deferred, as demonstrated by the `almost_montgomery_mul` method used
/// in `BoxedMontyMultiplier`.
#[inline(always)]
#[allow(clippy::cast_possible_truncation)]
pub const fn montgomery_multiply_inner(
    x: &[Limb],
    y: &[Limb],
    out: &mut [Limb],
    modulus: &[Limb],
    mod_neg_inv: Limb,
) -> Limb {
    let nlimbs = modulus.len();
    assert!(nlimbs == x.len() && nlimbs == y.len() && nlimbs == out.len());

    let mut meta_carry = 0;

    let mut i = 0;
    while i < nlimbs {
        let xi = x[i];
        // A[0] + x[i]y[0] <= (2^64 - 1)^2 + (2^64 - 1) = 2^128 - 2^64
        let axy = (xi.0 as WideWord) * (y[0].0 as WideWord) + out[0].0 as WideWord;
        let u = (axy as Word).wrapping_mul(mod_neg_inv.0);

        let mut carry;
        // A[0] + x[i]y[0] + um[0] <= (2^128 - 1) + (2^128 - 2^64) = 2^129 - 2^64 - 1
        let (a, c) = ((u as WideWord) * (modulus[0].0 as WideWord)).overflowing_add(axy);
        // carry <= (2^129 - 2^64 - 1) / 2^64 <= 2^65 - 2
        carry = ((c as WideWord) << Word::BITS) | (a >> Word::BITS);

        let mut j = 1;
        while j < nlimbs {
            // A[j] + x[i]y[j] <= (2^64 - 1)^2 + (2^64 - 1) = 2^128 - 2^64
            let axy = (xi.0 as WideWord) * (y[j].0 as WideWord) + out[j].0 as WideWord;
            // um[j] + carry <= (2^64 - 1)^2 + (2^65 - 2) = 2^128 - 1
            let umc = (u as WideWord) * (modulus[j].0 as WideWord) + carry;
            let (ab, c) = axy.overflowing_add(umc);
            out[j - 1] = Limb(ab as Word);
            // carry <= (2^129 - 2^64 - 1) / 2^64 <= 2^65 - 2
            carry = ((c as WideWord) << Word::BITS) | (ab >> Word::BITS);
            j += 1;
        }

        carry += meta_carry;
        (out[nlimbs - 1], meta_carry) = (Limb(carry as Word), carry >> Word::BITS);

        i += 1;
    }

    Limb(meta_carry as Word)
}

/// Computes the Montgomery product of `a` and `b` modulo `modulus`, where
/// `a` and `b` are in Montgomery form.
pub(crate) const fn mul_montgomery_form<const LIMBS: usize>(
    a: &Uint<LIMBS>,
    b: &Uint<LIMBS>,
    modulus: &Odd<Uint<LIMBS>>,
    mod_neg_inv: Limb,
) -> Uint<LIMBS> {
    let mut out = Uint::<LIMBS>::ZERO;
    let carry = montgomery_multiply_inner(
        &a.limbs,
        &b.limbs,
        &mut out.limbs,
        &modulus.0.limbs,
        mod_neg_inv,
    );
    out.sub_mod_with_carry(carry, modulus.as_ref(), modulus.as_ref())
}

/// Computes the Montgomery squaring of `a` modulo `modulus` where
/// `a` is in Montgomery form.
pub(crate) const fn square_montgomery_form<const LIMBS: usize>(
    a: &Uint<LIMBS>,
    modulus: &Odd<Uint<LIMBS>>,
    mod_neg_inv: Limb,
) -> Uint<LIMBS> {
    // One case in which it appears to be more efficient to perform a wide squaring and reduction.
    if LIMBS == 4 {
        let lower_upper = a.square_wide();
        return montgomery_reduction(&lower_upper, modulus, mod_neg_inv);
    }

    let mut out = Uint::<LIMBS>::ZERO;
    let carry = montgomery_multiply_inner(
        &a.limbs,
        &a.limbs,
        &mut out.limbs,
        &modulus.0.limbs,
        mod_neg_inv,
    );
    out.sub_mod_with_carry(carry, modulus.as_ref(), modulus.as_ref())
}

/// Computes a repeated Montgomery squaring of `a` modulo `modulus` where
/// `a` is in Montgomery form.
///
/// This method is variable time in `n`.
#[inline(always)]
pub(crate) const fn square_repeat_montgomery_form<const LIMBS: usize>(
    a: &Uint<LIMBS>,
    n: u32,
    modulus: &Odd<Uint<LIMBS>>,
    mod_neg_inv: Limb,
) -> Uint<LIMBS> {
    if n == 0 {
        return *a;
    }
    if n == 1 {
        return square_montgomery_form(a, modulus, mod_neg_inv);
    }

    let mut i = 0;
    let mut out = *a;
    let mut base;
    let mut carry;

    loop {
        (base, out) = (out, Uint::ZERO);
        carry = montgomery_multiply_inner(
            &base.limbs,
            &base.limbs,
            &mut out.limbs,
            &modulus.0.limbs,
            mod_neg_inv,
        );
        i += 1;
        if i == n {
            break;
        }
        // intermediate results are in "Almost Montgomery form", which is <= Uint::MAX
        // but may require the modulus to be subtracted twice.
        out = out
            .conditional_borrowing_sub(modulus.as_ref(), carry.is_nonzero())
            .0;
    }

    // correct for "Almost Montygomery form"
    out = out.sub_mod_with_carry(carry, modulus.as_ref(), modulus.as_ref());
    out.sub_mod_with_carry(Limb::ZERO, modulus.as_ref(), modulus.as_ref())
}
