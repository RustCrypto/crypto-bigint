use crate::{
    uint::{
        add::add2,
        sub::{sub2, sub_sign, Sign},
    },
    Limb,
};

use super::mul_limbs as mac3;

/// Karatsuba multiplication:
///
/// The idea is that we break x and y up into two smaller numbers that each have about half
/// as many digits, like so (note that multiplying by b is just a shift):
///
/// x = x0 + x1 * b
/// y = y0 + y1 * b
///
/// With some algebra, we can compute x * y with three smaller products, where the inputs to
/// each of the smaller products have only about half as many digits as x and y:
///
/// x * y = (x0 + x1 * b) * (y0 + y1 * b)
///
/// x * y = x0 * y0
///       + x0 * y1 * b
///       + x1 * y0 * b       + x1 * y1 * b^2
///
/// Let p0 = x0 * y0 and p2 = x1 * y1:
///
/// x * y = p0
///       + (x0 * y1 + x1 * y0) * b
///       + p2 * b^2
///
/// The real trick is that middle term:
///
///   x0 * y1 + x1 * y0
/// = x0 * y1 + x1 * y0 - p0 + p0 - p2 + p2
/// = x0 * y1 + x1 * y0 - x0 * y0 - x1 * y1 + p0 + p2
///
/// Now we complete the square:
///
/// = -(x0 * y0 - x0 * y1 - x1 * y0 + x1 * y1) + p0 + p2
/// = -((x1 - x0) * (y1 - y0)) + p0 + p2
///
/// Let p1 = (x1 - x0) * (y1 - y0), and substitute back into our original formula:
///
/// x * y = p0
///       + (p0 + p2 - p1) * b
///       + p2 * b^2
///
/// Where the three intermediate products are:
///
/// p0 = x0 * y0
/// p1 = (x1 - x0) * (y1 - y0)
/// p2 = x1 * y1
///
/// In doing the computation, we take great care to avoid unnecessary temporary variables
/// (since creating a BigUint requires a heap allocation): thus, we rearrange the formula a
/// bit so we can use the same temporary variable for all the intermediate products:
///
/// x * y = p2 * b^2 + p2 * b
///       + p0 * b + p0
///       - p1 * b
///
/// The other trick we use is instead of doing explicit shifts, we slice acc at the
/// appropriate offset when doing the add.
pub(super) fn mul(x: &[Limb], y: &[Limb], acc: &mut [Limb]) {
    debug_assert_eq!(x.len(), y.len());
    let b = x.len() / 2;
    let (x0, x1) = x.split_at(b);
    let (y0, y1) = y.split_at(b);

    // We reuse the same container for all the intermediate multiplies and have to size p
    // appropriately here.
    let len = x1.len() + y1.len();
    let mut p = vec![Limb::ZERO; len];

    // p2 = x1 * y1
    mac3(x1, y1, &mut p[..]);

    add2(&mut acc[b..], &p[..]);
    add2(&mut acc[b * 2..], &p[..]);

    // Zero out p before the next multiply:
    clear(&mut p);

    // p0 = x0 * y0
    mac3(x0, y0, &mut p[..x0.len() + y0.len()]);

    add2(&mut acc[..], &p[..]);
    add2(&mut acc[b..], &p[..]);

    // p1 = (x1 - x0) * (y1 - y0)
    // We do this one last, since it may be negative and acc can't ever be negative:
    let (j0_sign, j0) = sub_sign(x1, x0);
    let (j1_sign, j1) = sub_sign(y1, y0);

    match (j0_sign, j1_sign) {
        (Sign::Plus, Sign::Plus) | (Sign::Minus, Sign::Minus) => {
            clear(&mut p);

            mac3(&j0[..], &j1[..], &mut p[..]);
            sub2(&mut acc[b..], &p[..]);
        }
        (Sign::Minus, Sign::Plus) | (Sign::Plus, Sign::Minus) => {
            mac3(&j0[..], &j1[..], &mut acc[b..]);
        }
        (Sign::NoSign, _) | (_, Sign::NoSign) => {}
    }
}

fn clear(v: &mut [Limb]) {
    for el in v {
        el.0 = 0;
    }
}
