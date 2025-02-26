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
pub(crate) fn almost_montgomery_mul(
    z_lower: &mut [Limb],
    z_upper: &mut [Limb],
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
    let pre_cond =
        z_upper.len() == n && z_lower.len() == n && x.len() == n && y.len() == n && m.len() == n;
    if !pre_cond {
        panic!(
            "Failed preconditions in montgomery_mul: {} {} {} {} {}",
            z_lower.len(),
            z_upper.len(),
            x.len(),
            y.len(),
            m.len()
        );
    }

    let mut c = ConstChoice::FALSE;

    let mut i = 0;
    while i < n {
        let c2 = add_mul_vvw(z_lower, z_upper, i, x, y[i]);
        let t = z_lower[i].wrapping_mul(k);
        let c3 = add_mul_vvw(z_lower, z_upper, i, m, t);
        let cx = c2.wrapping_add(Limb(c.to_u8() as Word));
        let cy = cx.wrapping_add(c3);
        z_upper[i] = cy;
        c = ConstChoice::from_word_lt(cx.0, c2.0).or(ConstChoice::from_word_lt(cy.0, c3.0));
        i += 1;
    }

    sub_vv(z_lower, z_upper, m);

    let is_zero = c.not();
    let mut i = 0;
    while i < n {
        z_lower[i] = Limb::select(z_lower[i], z_upper[i], is_zero);
        i += 1;
    }
}

/// Same as `almost_montgomery_mul` with `y == 1`.
///
/// Used for retrieving from Montgomery form.
pub(crate) fn almost_montgomery_mul_by_one(
    z_lower: &mut [Limb],
    z_upper: &mut [Limb],
    x: &[Limb],
    m: &[Limb],
    k: Limb,
) {
    // This code assumes x, m are all the same length (required by addMulVVW and the for loop).
    // It also assumes that x is already reduced mod m, or else the result will not be properly
    // reduced.
    let n = m.len();

    // This preconditions check allows compiler to remove bound checks later in the code.
    let pre_cond = z_upper.len() == n && z_lower.len() == n && x.len() == n && m.len() == n;
    if !pre_cond {
        panic!(
            "Failed preconditions in montgomery_mul {} {} {} {}",
            z_lower.len(),
            z_upper.len(),
            x.len(),
            m.len()
        );
    }

    let mut c = ConstChoice::FALSE;

    // The unrolled first iteration.
    let c2 = add_mul_vvw(z_lower, z_upper, 0, x, Limb::ONE);
    let t = z_lower[0].wrapping_mul(k);
    let c3 = add_mul_vvw(z_lower, z_upper, 0, m, t);
    let cx = c2.wrapping_add(Limb(c.to_u8() as Word));
    let cy = cx.wrapping_add(c3);
    z_upper[0] = cy;
    c = ConstChoice::from_word_lt(cx.0, c2.0).or(ConstChoice::from_word_lt(cy.0, c3.0));

    let mut i = 1;
    while i < n {
        let c2 = add_mul_vvw(z_lower, z_upper, i, x, Limb::ZERO);
        let t = z_lower[i].wrapping_mul(k);
        let c3 = add_mul_vvw(z_lower, z_upper, i, m, t);
        let cx = c2.wrapping_add(Limb(c.to_u8() as Word));
        let cy = cx.wrapping_add(c3);
        z_upper[i] = cy;
        c = ConstChoice::from_word_lt(cx.0, c2.0).or(ConstChoice::from_word_lt(cy.0, c3.0));
        i += 1;
    }

    sub_vv(z_lower, z_upper, m);

    let is_zero = c.not();
    let mut i = 0;
    while i < n {
        z_lower[i] = Limb::select(z_lower[i], z_upper[i], is_zero);
        i += 1;
    }
}

#[inline]
const fn add_mul_vvw(
    z_lower: &mut [Limb],
    z_upper: &mut [Limb],
    z_offset: usize,
    x: &[Limb],
    y: Limb,
) -> Limb {
    let mut c = Limb::ZERO;

    let mut i = 0;
    let (_, z) = z_lower.split_at_mut(z_offset);
    while i < z.len() && i < x.len() {
        let (z0, z1) = z[i].mac(x[i], y, Limb::ZERO);
        let (zi_, c_) = z0.overflowing_add(c);
        z[i] = zi_;
        c = c_.wrapping_add(z1);
        i = i.wrapping_add(1);
    }

    let mut i = 0;
    let (_, x_upper) = x.split_at(x.len().wrapping_sub(z_offset));
    while i < x_upper.len() && i < z_upper.len() {
        let (z0, z1) = z_upper[i].mac(x_upper[i], y, Limb::ZERO);
        let (zi_, c_) = z0.overflowing_add(c);
        z_upper[i] = zi_;
        c = c_.wrapping_add(z1);
        i = i.wrapping_add(1);
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
