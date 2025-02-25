use crate::{ConstChoice, Limb, Word};

/// Compute an "Almost Montgomery Multiplication (AMM)" as described in the paper
/// "Efficient Software Implementations of Modular Exponentiation"
/// <https://eprint.iacr.org/2011/239.pdf>
///
/// NOTE: `z` is assumed to be pre-zeroized.
///
/// Computes z mod m = x * y * 2 ** (-n*_W) mod m assuming k = -1/m mod 2**_W.
///
/// x and y are required to satisfy 0 <= z < 2**(n*_W) and then the result z is guaranteed to
/// satisfy 0 <= z < 2**(n*_W), but it may not be < m.
///
/// Output is written into the lower (i.e. first) half of `z`.
///
/// Note: this was adapted from an implementation in `num-bigint`'s `monty.rs`.
// TODO(tarcieri): refactor into `reduction.rs`, share impl with `MontyForm`?
pub(crate) fn almost_montgomery_mul(z: &mut [Limb], x: &[Limb], y: &[Limb], m: &[Limb], k: Limb) {
    // This code assumes x, y, m are all the same length (required by addMulVVW and the for loop).
    // It also assumes that x, y are already reduced mod m, or else the result will not be properly
    // reduced.
    let n = m.len();

    // This preconditions check allows compiler to remove bound checks later in the code.
    // `z.len() > n && z[n..].len() == n` is used intentionally instead of `z.len() == 2* n`
    // since the latter prevents compiler from removing some bound checks.
    let pre_cond = z.len() > n && z[n..].len() == n && x.len() == n && y.len() == n && m.len() == n;
    if !pre_cond {
        panic!("Failed preconditions in montgomery_mul");
    }

    let mut c = ConstChoice::FALSE;

    for i in 0..n {
        let c2 = add_mul_vvw(&mut z[i..n + i], x, y[i]);
        let t = z[i].wrapping_mul(k);
        let c3 = add_mul_vvw(&mut z[i..n + i], m, t);
        let cx = c2.wrapping_add(Limb(c.to_u8() as Word));
        let cy = cx.wrapping_add(c3);
        z[n + i] = cy;
        c = ConstChoice::from_word_lt(cx.0, c2.0).or(ConstChoice::from_word_lt(cy.0, c3.0));
    }

    let (lower, upper) = z.split_at_mut(n);
    sub_vv(lower, upper, m);

    let is_zero = c.not();
    for (a, b) in lower.iter_mut().zip(upper.iter()) {
        *a = Limb::select(*a, *b, is_zero);
    }
}

/// Same as `almost_montgomery_mul` with `y == 1`.
///
/// Used for retrieving from Montgomery form.
pub(crate) fn almost_montgomery_mul_by_one(z: &mut [Limb], x: &[Limb], m: &[Limb], k: Limb) {
    // This code assumes x, m are all the same length (required by addMulVVW and the for loop).
    // It also assumes that x is already reduced mod m, or else the result will not be properly
    // reduced.
    let n = m.len();

    // This preconditions check allows compiler to remove bound checks later in the code.
    // `z.len() > n && z[n..].len() == n` is used intentionally instead of `z.len() == 2* n`
    // since the latter prevents compiler from removing some bound checks.
    let pre_cond = z.len() > n && z[n..].len() == n && x.len() == n && m.len() == n;
    if !pre_cond {
        panic!("Failed preconditions in montgomery_mul");
    }

    let mut c = ConstChoice::FALSE;

    // The unrolled first iteration.
    let c2 = add_mul_vvw(&mut z[0..n], x, Limb::ONE);
    let t = z[0].wrapping_mul(k);
    let c3 = add_mul_vvw(&mut z[0..n], m, t);
    let cx = c2.wrapping_add(Limb(c.to_u8() as Word));
    let cy = cx.wrapping_add(c3);
    z[n] = cy;
    c = ConstChoice::from_word_lt(cx.0, c2.0).or(ConstChoice::from_word_lt(cy.0, c3.0));

    for i in 1..n {
        let c2 = add_mul_vvw(&mut z[i..n + i], x, Limb::ZERO);
        let t = z[i].wrapping_mul(k);
        let c3 = add_mul_vvw(&mut z[i..n + i], m, t);
        let cx = c2.wrapping_add(Limb(c.to_u8() as Word));
        let cy = cx.wrapping_add(c3);
        z[n + i] = cy;
        c = ConstChoice::from_word_lt(cx.0, c2.0).or(ConstChoice::from_word_lt(cy.0, c3.0));
    }

    let (lower, upper) = z.split_at_mut(n);
    sub_vv(lower, upper, m);

    let is_zero = c.not();
    for (a, b) in lower.iter_mut().zip(upper.iter()) {
        *a = Limb::select(*a, *b, is_zero);
    }
}

#[inline]
fn add_mul_vvw(z: &mut [Limb], x: &[Limb], y: Limb) -> Limb {
    let mut c = Limb::ZERO;

    for (zi, xi) in z.iter_mut().zip(x.iter()) {
        let (z0, z1) = zi.mac(*xi, y, Limb::ZERO);
        let (zi_, c_) = z0.overflowing_add(c);
        *zi = zi_;
        c = c_.wrapping_add(z1);
    }

    c
}

#[inline(always)]
fn sub_vv(z: &mut [Limb], x: &[Limb], y: &[Limb]) {
    let mut borrow = Limb::ZERO;
    for (i, (&xi, &yi)) in x.iter().zip(y.iter()).enumerate().take(z.len()) {
        let (zi, new_borrow) = xi.sbb(yi, borrow);
        z[i] = zi;
        borrow = new_borrow;
    }
}
