//! Implementation of constant-time division via reciprocal precomputation, as described in
//! "Improved Division by Invariant Integers" by Niels Möller and Torbjorn Granlund
//! (DOI: 10.1109/TC.2010.143, <https://gmplib.org/~tege/division-paper.pdf>).
use crate::{uint::div_limb::div2by1, BoxedUint, Limb, Reciprocal};

/// Divides `u` by the divisor encoded in the `reciprocal`, and returns
/// the quotient and the remainder.
#[inline(always)]
pub(crate) fn div_rem_limb_with_reciprocal(
    u: &BoxedUint,
    reciprocal: &Reciprocal,
) -> (BoxedUint, Limb) {
    let (u_shifted, u_hi) = u.shl_limb(reciprocal.shift());
    let mut r = u_hi.0;
    let mut q = vec![Limb::ZERO; u.limbs.len()];

    let mut j = u.limbs.len();
    while j > 0 {
        j -= 1;
        let (qj, rj) = div2by1(r, u_shifted.as_limbs()[j].0, reciprocal);
        q[j] = Limb(qj);
        r = rj;
    }
    (BoxedUint { limbs: q.into() }, Limb(r >> reciprocal.shift()))
}

/// Divides `u` by the divisor encoded in the `reciprocal`, and returns the remainder.
#[inline(always)]
pub(crate) fn rem_limb_with_reciprocal(u: &BoxedUint, reciprocal: &Reciprocal) -> Limb {
    let (u_shifted, u_hi) = u.shl_limb(reciprocal.shift());
    let mut r = u_hi.0;

    let mut j = u.limbs.len();
    while j > 0 {
        j -= 1;
        let (_, rj) = div2by1(r, u_shifted.as_limbs()[j].0, reciprocal);
        r = rj;
    }
    Limb(r >> reciprocal.shift())
}
