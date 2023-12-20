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

#[cfg(test)]
mod tests {
    use super::{div2by1, Reciprocal};
    use crate::{Limb, NonZero, Word};
    #[test]
    fn div2by1_overflow() {
        // A regression test for a situation when in div2by1() an operation (`q1 + 1`)
        // that is protected from overflowing by a condition in the original paper (`r >= d`)
        // still overflows because we're calculating the results for both branches.
        let r = Reciprocal::new(NonZero::new(Limb(Word::MAX - 1)).unwrap());
        assert_eq!(
            div2by1(Word::MAX - 2, Word::MAX - 63, &r),
            (Word::MAX, Word::MAX - 65)
        );
    }
}
