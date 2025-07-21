//! Implementation of Bernstein-Yang modular inversion and GCD algorithm (a.k.a. safegcd)
//! as described in: <https://eprint.iacr.org/2019/266>.
//!
//! Adapted from the Apache 2.0+MIT licensed implementation originally from:
//! <https://github.com/taikoxyz/halo2curves/pull/2>
//! <https://github.com/privacy-scaling-explorations/halo2curves/pull/83>
//!
//! Copyright (c) 2023 Privacy Scaling Explorations Team

// TODO(tarcieri): optimized implementation for 32-bit platforms (#380)

#![allow(clippy::needless_range_loop)]

#[cfg(feature = "alloc")]
pub(crate) mod boxed;

use core::fmt;

use crate::{
    ConstChoice, ConstCtOption, I64, Int, Inverter, Limb, Odd, U64, Uint, Word,
    const_choice::u32_min,
};
use subtle::CtOption;

const GCD_BATCH_SIZE: u32 = 62;

/// Modular multiplicative inverter based on the Bernstein-Yang method.
///
/// The inverter can be created for a specified modulus M and adjusting parameter A to compute
/// the adjusted multiplicative inverses of positive integers, i.e. for computing
/// (1 / x) * A (mod M) for a positive integer x.
///
/// The adjusting parameter allows computing the multiplicative inverses in the case of using the
/// Montgomery representation for the input or the expected output. If R is the Montgomery
/// factor, the multiplicative inverses in the appropriate representation can be computed
/// provided that the value of A is chosen as follows:
/// - A = 1, if both the input and the expected output are in the standard form
/// - A = R^2 mod M, if both the input and the expected output are in the Montgomery form
/// - A = R mod M, if either the input or the expected output is in the Montgomery form,
///   but not both of them
///
/// The public methods of this type receive and return unsigned big integers as arrays of 64-bit
/// chunks, the ordering of which is little-endian. Both the modulus and the integer to be
/// inverted should not exceed 2 ^ (62 * L - 64).
///
/// For better understanding the implementation, the following resources are recommended:
/// - D. Bernstein, B.-Y. Yang, "Fast constant-time gcd computation and modular inversion",
///   <https://gcd.cr.yp.to/safegcd-20190413.pdf>
/// - P. Wuille, "The safegcd implementation in libsecp256k1 explained",
///   <https://github.com/bitcoin-core/secp256k1/blob/master/doc/safegcd_implementation.md>
#[derive(Clone, Debug)]
pub struct SafeGcdInverter<const LIMBS: usize> {
    /// Modulus
    pub(super) modulus: Odd<Uint<LIMBS>>,

    /// Adjusting parameter (see toplevel documentation).
    adjuster: Uint<LIMBS>,

    /// Multiplicative inverse of the modulus modulo 2^62
    inverse: u64,
}

/// Type of the Bernstein-Yang transition matrix multiplied by 2^62
type Matrix = [[i64; 2]; 2];

impl<const LIMBS: usize> SafeGcdInverter<LIMBS> {
    /// Creates the inverter for specified modulus and adjusting parameter.
    ///
    /// Modulus must be odd. Returns `None` if it is not.
    pub const fn new(modulus: &Odd<Uint<LIMBS>>, adjuster: &Uint<LIMBS>) -> Self {
        Self {
            modulus: *modulus,
            adjuster: *adjuster,
            inverse: invert_mod2_62(modulus.0.as_words()),
        }
    }

    /// Returns either the adjusted modular multiplicative inverse for the argument or `None`
    /// depending on invertibility of the argument, i.e. its coprimality with the modulus.
    #[deprecated(since = "0.7.0", note = "please use `invert` instead")]
    pub fn inv(&self, value: &Uint<LIMBS>) -> ConstCtOption<Uint<LIMBS>> {
        self.invert(value)
    }

    /// Returns either the adjusted modular multiplicative inverse for the argument or `None`
    /// depending on invertibility of the argument, i.e. its coprimality with the modulus.
    pub const fn invert(&self, value: &Uint<LIMBS>) -> ConstCtOption<Uint<LIMBS>> {
        invert_mod_precomp::<LIMBS, false>(value, &self.modulus, &self.adjuster, self.inverse)
    }

    /// Returns either the adjusted modular multiplicative inverse for the argument or `None`
    /// depending on invertibility of the argument, i.e. its coprimality with the modulus.
    ///
    /// This version is variable-time with respect to `value`.
    #[deprecated(since = "0.7.0", note = "please use `invert_vartime` instead")]
    pub const fn inv_vartime(&self, value: &Uint<LIMBS>) -> ConstCtOption<Uint<LIMBS>> {
        self.invert_vartime(value)
    }

    /// Returns either the adjusted modular multiplicative inverse for the argument or `None`
    /// depending on invertibility of the argument, i.e. its coprimality with the modulus.
    ///
    /// This version is variable-time with respect to `value`.
    pub const fn invert_vartime(&self, value: &Uint<LIMBS>) -> ConstCtOption<Uint<LIMBS>> {
        invert_mod_precomp::<LIMBS, true>(value, &self.modulus, &self.adjuster, self.inverse)
    }
}

impl<const LIMBS: usize> Inverter for SafeGcdInverter<LIMBS> {
    type Output = Uint<LIMBS>;

    fn invert(&self, value: &Uint<LIMBS>) -> CtOption<Self::Output> {
        self.invert(value).into()
    }

    fn invert_vartime(&self, value: &Uint<LIMBS>) -> CtOption<Self::Output> {
        self.invert_vartime(value).into()
    }
}

/// Returns the multiplicative inverse of the argument modulo 2^62. The implementation is based
/// on the Hurchalla's method for computing the multiplicative inverse modulo a power of two.
///
/// For better understanding the implementation, the following paper is recommended:
/// J. Hurchalla, "An Improved Integer Multiplicative Inverse (modulo 2^w)",
/// <https://arxiv.org/pdf/2204.04342.pdf>
///
/// Variable time with respect to the number of words in `value`, however that number will be
/// fixed for a given integer size.
const fn invert_mod2_62(value: &[Word]) -> u64 {
    let value = {
        #[cfg(target_pointer_width = "32")]
        {
            debug_assert!(value.len() >= 1);
            let mut ret = value[0] as u64;

            if value.len() >= 2 {
                ret |= (value[1] as u64) << 32;
            }

            ret
        }

        #[cfg(target_pointer_width = "64")]
        {
            value[0]
        }
    };

    let x = value.wrapping_mul(3) ^ 2;
    let y = 1u64.wrapping_sub(x.wrapping_mul(value));
    let (x, y) = (x.wrapping_mul(y.wrapping_add(1)), y.wrapping_mul(y));
    let (x, y) = (x.wrapping_mul(y.wrapping_add(1)), y.wrapping_mul(y));
    let (x, y) = (x.wrapping_mul(y.wrapping_add(1)), y.wrapping_mul(y));
    x.wrapping_mul(y.wrapping_add(1)) & (u64::MAX >> 2)
}

pub const fn invert_mod<const LIMBS: usize, const VARTIME: bool>(
    a: &Uint<LIMBS>,
    m: &Odd<Uint<LIMBS>>,
) -> ConstCtOption<Uint<LIMBS>> {
    let mi = invert_mod2_62(m.as_ref().as_words());
    invert_mod_precomp::<LIMBS, VARTIME>(a, m, &Uint::ONE, mi)
}

pub const fn invert_mod_precomp<const LIMBS: usize, const VARTIME: bool>(
    a: &Uint<LIMBS>,
    m: &Odd<Uint<LIMBS>>,
    e: &Uint<LIMBS>,
    mi: u64,
) -> ConstCtOption<Uint<LIMBS>> {
    let (f, d, _) = xgcd_precomp::<LIMBS, VARTIME>(m, a, e, mi);
    let d = d.norm(f.sign, m.as_ref());
    ConstCtOption::new(d, Uint::eq(&f.magnitude, &Uint::ONE))
}

pub const fn gcd<const LIMBS: usize>(f: &Odd<Uint<LIMBS>>, g: &Uint<LIMBS>) -> Uint<LIMBS> {
    let (mut f, mut g) = (Sint::from_uint(*f.as_ref()), Sint::from_uint(*g));
    let mut steps = iterations(Uint::<LIMBS>::BITS);
    let mut delta = 1;
    let mut t;

    while steps > 0 {
        let batch = u32_min(steps, GCD_BATCH_SIZE);
        (delta, t) = gcd_jump(f.lowest(), g.lowest(), delta, batch);
        (f, g) = update_fg(&f, &g, t, batch);
        steps -= batch;
    }

    f.abs()
}

const fn xgcd_precomp<const LIMBS: usize, const VARTIME: bool>(
    f: &Odd<Uint<LIMBS>>,
    g: &Uint<LIMBS>,
    e: &Uint<LIMBS>,
    mi: u64,
) -> (Sint<LIMBS>, Sint<LIMBS>, Sint<LIMBS>) {
    let m = f;
    let (mut f, mut g) = (Sint::from_uint(*f.as_ref()), Sint::from_uint(*g));
    let (mut d, mut e) = (Sint::<LIMBS>::ZERO, Sint::from_uint(*e));
    let mut steps = iterations(Uint::<LIMBS>::BITS);
    let mut delta = 1;
    let mut t;

    while steps > 0 {
        if VARTIME && g.is_zero().to_bool_vartime() {
            break;
        }
        let batch = u32_min(steps, GCD_BATCH_SIZE);
        (delta, t) = gcd_jump(f.lowest(), g.lowest(), delta, batch);
        (f, g) = update_fg(&f, &g, t, batch);
        (d, e) = update_de(&d, &e, t, batch, m.as_ref(), U64::from_u64(mi));
        steps -= batch;
    }

    (f, d, e)
}

const fn gcd_jump(mut f: u64, mut g: u64, mut delta: i64, mut batch: u32) -> (i64, Matrix) {
    let mut t = [[1i64, 0], [0, 1]];
    while batch > 0 {
        (f, g, delta, t) = gcd_jump_core(f, g, delta, t);
        batch -= 1;
    }
    (delta, t)
}

#[inline(always)]
const fn gcd_jump_core(
    mut f: u64,
    mut g: u64,
    mut delta: i64,
    mut t: Matrix,
) -> (u64, u64, i64, Matrix) {
    let d_pnz = ConstChoice::from_u64_lsb(!(delta as u64) >> 63);
    let g_odd = ConstChoice::from_u64_lsb(g & 1);
    let g_adj = g_odd.select_u64(0, f);
    let b1 = d_pnz.and(g_odd);
    delta = b1.select_i64(2 + delta, 2 - delta);
    f = b1.select_u64(f, g);
    g = b1.select_u64(g.wrapping_add(g_adj), g.wrapping_sub(g_adj)) >> 1;

    let t0 = t[1][0] + g_odd.select_i64(0, d_pnz.select_i64(t[0][0], -t[0][0]));
    let t1 = t[1][1] + g_odd.select_i64(0, d_pnz.select_i64(t[0][1], -t[0][1]));
    t = [
        [
            b1.select_i64(t[0][0], t[1][0]) << 1,
            b1.select_i64(t[0][1], t[1][1]) << 1,
        ],
        [t0, t1],
    ];
    (f, g, delta, t)
}

#[inline]
const fn update_fg<const LIMBS: usize>(
    a: &Sint<LIMBS>,
    b: &Sint<LIMBS>,
    t: Matrix,
    batch: u32,
) -> (Sint<LIMBS>, Sint<LIMBS>) {
    const fn update_term<const LIMBS: usize, const S: usize>(
        a: &Sint<LIMBS>,
        b: &Sint<LIMBS>,
        row: &(Int<S>, Int<S>),
        batch: u32,
    ) -> Sint<LIMBS> {
        let (mut a, mut a_hi, a_sign) = Sint::lincomb_uint_int(a, b, &row.0, &row.1);

        a = a.shr_vartime(batch);
        (a_hi, _) = a_hi.shl_limb(Uint::<S>::BITS - batch);
        a.limbs[LIMBS - S] = a.limbs[LIMBS - S].bitor(a_hi.limbs[0]);
        let mut i = 1;
        while i < S {
            a.limbs[LIMBS - i] = a_hi.limbs[S - i];
            i += 1;
        }

        Sint::from_uint_sign(a, a_sign)
    }

    (
        update_term(
            a,
            b,
            &(I64::from_i64(t[0][0]), I64::from_i64(t[0][1])),
            batch,
        ),
        update_term(
            a,
            b,
            &(I64::from_i64(t[1][0]), I64::from_i64(t[1][1])),
            batch,
        ),
    )
}

#[inline]
const fn update_de<const LIMBS: usize, const S: usize>(
    d: &Sint<LIMBS>,
    e: &Sint<LIMBS>,
    t: Matrix,
    batch: u32,
    m: &Uint<LIMBS>,
    mi: Uint<S>,
) -> (Sint<LIMBS>, Sint<LIMBS>) {
    const fn update_term<const LIMBS: usize, const S: usize>(
        d: &Sint<LIMBS>,
        e: &Sint<LIMBS>,
        t: &(Int<S>, Int<S>),
        batch: u32,
        m: &Uint<LIMBS>,
        mi: Uint<S>,
    ) -> Sint<LIMBS> {
        let (mut c, mut c_hi, mut c_sign) = Sint::lincomb_uint_int(d, e, &t.0, &t.1);
        let mut mf = c.resize::<S>().wrapping_mul(&mi);
        mf = mf.bitand(&Uint::MAX.shr_vartime(Uint::<S>::BITS - batch));
        let (ca, ca_hi) = m.widening_mul(&mf);

        let mut borrow;
        (c, borrow) = c.borrowing_sub(&ca, Limb::ZERO);
        (c_hi, borrow) = c_hi.borrowing_sub(&ca_hi, borrow);

        let swap = borrow.is_nonzero();
        conditional_negate_wide(&mut c, &mut c_hi, swap);
        c_sign = c_sign.xor(swap);

        c = c.shr_vartime(batch);
        let carry;
        (c_hi, carry) = c_hi.shl_limb(Uint::<S>::BITS - batch);
        c.limbs[LIMBS - S] = c.limbs[LIMBS - S].bitor(c_hi.limbs[0]);
        let mut i = 1;
        while i < S {
            c.limbs[LIMBS - i] = c_hi.limbs[S - i];
            i += 1;
        }

        let sub_m = carry.is_nonzero();
        c = c.wrapping_sub(&Uint::select(&Uint::ZERO, m, sub_m));

        Sint::from_uint_sign(c, c_sign)
    }

    (
        update_term(
            d,
            e,
            &(Int::from_i64(t[0][0]), Int::from_i64(t[0][1])),
            batch,
            m,
            mi,
        ),
        update_term(
            d,
            e,
            &(Int::from_i64(t[1][0]), Int::from_i64(t[1][1])),
            batch,
            m,
            mi,
        ),
    )
}

#[inline]
const fn conditional_negate_wide<const L: usize, const H: usize>(
    lo: &mut Uint<L>,
    hi: &mut Uint<H>,
    flag: ConstChoice,
) {
    let (neg, carry) = lo.carrying_neg();
    let hi_neg = hi
        .not()
        .wrapping_add(&Uint::select(&Uint::ZERO, &Uint::ONE, carry));
    *lo = Uint::select(lo, &neg, flag);
    *hi = Uint::select(hi, &hi_neg, flag);
}

#[inline]
const fn iterations(bits: u32) -> u32 {
    (45907 * bits + 26313) / 19929
}

struct Sint<const LIMBS: usize> {
    sign: ConstChoice,
    magnitude: Uint<LIMBS>,
}

impl<const LIMBS: usize> Sint<LIMBS> {
    const ZERO: Self = Self::from_uint(Uint::ZERO);
    const ONE: Self = Self::from_uint(Uint::ONE);

    const fn from_int(int: Int<LIMBS>) -> Self {
        let (magnitude, sign) = int.abs_sign();
        Self { sign, magnitude }
    }

    const fn from_uint(uint: Uint<LIMBS>) -> Self {
        Self {
            sign: ConstChoice::FALSE,
            magnitude: uint,
        }
    }

    const fn from_uint_sign(magnitude: Uint<LIMBS>, sign: ConstChoice) -> Self {
        Self { sign, magnitude }
    }

    const fn abs(&self) -> Uint<LIMBS> {
        self.magnitude
    }

    const fn is_zero(&self) -> ConstChoice {
        self.magnitude.is_nonzero().not()
    }

    const fn lowest(&self) -> u64 {
        // FIXME support 32 bit
        let mag = self.magnitude.as_words()[0];
        self.sign.select_u64(mag, mag.wrapping_neg())
    }

    #[inline]
    const fn lincomb_uint_int<const RHS: usize>(
        a: &Sint<LIMBS>,
        b: &Sint<LIMBS>,
        c: &Int<RHS>,
        d: &Int<RHS>,
    ) -> (Uint<LIMBS>, Uint<RHS>, ConstChoice) {
        let (c, c_sign) = c.abs_sign();
        let (d, d_sign) = d.abs_sign();
        // Each uint * abs(int) leaves an empty upper bit
        let (mut x, mut x_hi) = a.magnitude.widening_mul(&c);
        let x_neg = a.sign.xor(c_sign);
        let (mut y, mut y_hi) = b.magnitude.widening_mul(&d);
        let y_neg = b.sign.xor(d_sign);
        let odd_neg = x_neg.xor(y_neg);

        // Negate y if none or both of the multiplication results are negative.
        conditional_negate_wide(&mut y, &mut y_hi, odd_neg.not());

        let mut borrow;
        (x, borrow) = x.borrowing_sub(&y, Limb::ZERO);
        (x_hi, borrow) = x_hi.borrowing_sub(&y_hi, borrow);
        let swap = borrow.is_nonzero().and(odd_neg);

        conditional_negate_wide(&mut x, &mut x_hi, swap);

        let sign = x_neg.and(swap.not()).or(y_neg.and(swap));
        (x, x_hi, sign)
    }

    const fn to_int(&self) -> Int<LIMBS> {
        // Note: does not perform bounds checking
        Int::select(
            self.magnitude.as_int(),
            self.magnitude.wrapping_neg().as_int(),
            self.sign,
        )
    }

    const fn norm(&self, f_sign: ConstChoice, m: &Uint<LIMBS>) -> Uint<LIMBS> {
        let sign = f_sign.xor(self.sign);
        Uint::select(&self.magnitude, &m.wrapping_sub(&self.magnitude), sign)
    }
}

impl<const LIMBS: usize> fmt::Debug for Sint<LIMBS> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_fmt(format_args!(
            "{}0x{}",
            if self.sign.is_true_vartime() {
                "-"
            } else {
                "+"
            },
            &self.magnitude
        ))
    }
}

#[cfg(test)]
mod tests {
    use crate::{PrecomputeInverter, U256};

    #[test]
    fn invert() {
        let g =
            U256::from_be_hex("00000000CBF9350842F498CE441FC2DC23C7BF47D3DE91C327B2157C5E4EED77");
        let modulus =
            U256::from_be_hex("FFFFFFFF00000000FFFFFFFFFFFFFFFFBCE6FAADA7179E84F3B9CAC2FC632551")
                .to_odd()
                .unwrap();
        let inverter = modulus.precompute_inverter();
        let result = inverter.invert(&g).unwrap();
        assert_eq!(
            U256::from_be_hex("FB668F8F509790BC549B077098918604283D42901C92981062EB48BC723F617B"),
            result
        );
    }
}
