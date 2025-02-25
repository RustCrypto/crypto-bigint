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
pub(crate) const fn almost_montgomery_mul(
    z: &mut [Limb],
    x: &[Limb],
    y: &[Limb],
    m: &[Limb],
    k: Limb,
) {
    // This code assumes x, y, m are all the same length (required by addMulVVW and the for loop).
    // It also assumes that x, y are already reduced mod m, or else the result will not be properly
    // reduced.
    let n = m.len();

    // This preconditions check allows compiler to remove bound checks later in the code.
    let pre_cond = z.len() > n && x.len() == n && y.len() == n && m.len() == n;
    if !pre_cond {
        panic!("Failed preconditions in montgomery_mul");
    }

    let mut c = ConstChoice::FALSE;

    let mut i = 0;
    while i < n {
        let (_, mut z_slice) = z.split_at_mut(i);
        let c2 = add_mul_vvw(&mut z_slice, x, y[i]);
        let t = z_slice[0].wrapping_mul(k);
        let c3 = add_mul_vvw(&mut z_slice, m, t);
        let cx = c2.wrapping_add(Limb(c.to_u8() as Word));
        let cy = cx.wrapping_add(c3);
        z[n + i] = cy;
        c = ConstChoice::from_word_lt(cx.0, c2.0).or(ConstChoice::from_word_lt(cy.0, c3.0));
        i += 1;
    }

    let (lower, upper) = z.split_at_mut(n);
    sub_vv(lower, upper, m);

    let is_zero = c.not();
    let mut i = 0;
    while i < n {
        lower[i] = Limb::select(lower[i], upper[i], is_zero);
        i += 1;
    }
}

/// Same as `almost_montgomery_mul` with `y == 1`.
///
/// Used for retrieving from Montgomery form.
pub(crate) const fn almost_montgomery_mul_by_one(z: &mut [Limb], x: &[Limb], m: &[Limb], k: Limb) {
    // This code assumes x, m are all the same length (required by addMulVVW and the for loop).
    // It also assumes that x is already reduced mod m, or else the result will not be properly
    // reduced.
    let n = m.len();

    // This preconditions check allows compiler to remove bound checks later in the code.
    let pre_cond = z.len() > n && x.len() == n && m.len() == n;
    if !pre_cond {
        panic!("Failed preconditions in montgomery_mul");
    }

    let mut c = ConstChoice::FALSE;

    // The unrolled first iteration.
    let c2 = add_mul_vvw(z, x, Limb::ONE);
    let t = z[0].wrapping_mul(k);
    let c3 = add_mul_vvw(z, m, t);
    let cx = c2.wrapping_add(Limb(c.to_u8() as Word));
    let cy = cx.wrapping_add(c3);
    z[n] = cy;
    c = ConstChoice::from_word_lt(cx.0, c2.0).or(ConstChoice::from_word_lt(cy.0, c3.0));

    let mut i = 1;
    while i < n {
        let (_, mut z_slice) = z.split_at_mut(i);
        let c2 = add_mul_vvw(&mut z_slice, x, Limb::ZERO);
        let t = z_slice[0].wrapping_mul(k);
        let c3 = add_mul_vvw(&mut z_slice, m, t);
        let cx = c2.wrapping_add(Limb(c.to_u8() as Word));
        let cy = cx.wrapping_add(c3);
        z[n + i] = cy;
        c = ConstChoice::from_word_lt(cx.0, c2.0).or(ConstChoice::from_word_lt(cy.0, c3.0));
        i += 1;
    }

    let (lower, upper) = z.split_at_mut(n);
    sub_vv(lower, upper, m);

    let is_zero = c.not();
    let mut i = 0;
    while i < n {
        lower[i] = Limb::select(lower[i], upper[i], is_zero);
        i += 1;
    }
}

#[inline]
const fn add_mul_vvw(z: &mut [Limb], x: &[Limb], y: Limb) -> Limb {
    let n = x.len();
    if n > z.len() {
        panic!("Failed preconditions in montgomery_mul");
    }

    let mut c = Limb::ZERO;

    let mut i = 0;
    while i < n {
        let (z0, z1) = z[i].mac(x[i], y, Limb::ZERO);
        let (zi_, c_) = z0.overflowing_add(c);
        z[i] = zi_;
        c = c_.wrapping_add(z1);
        i += 1;
    }

    c
}

#[inline(always)]
const fn sub_vv(z: &mut [Limb], x: &[Limb], y: &[Limb]) {
    let n = z.len();
    if !(n == x.len() && n == y.len()) {
        panic!("Failed preconditions in montgomery_mul");
    }

    let mut borrow = Limb::ZERO;

    let mut i = 0;
    while i < n {
        let (zi, new_borrow) = x[i].sbb(y[i], borrow);
        z[i] = zi;
        borrow = new_borrow;
        i += 1;
    }
}
