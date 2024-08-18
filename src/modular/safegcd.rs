//! Implementation of Bernstein-Yang modular inversion and GCD algorithm (a.k.a. safegcd)
//! as described in: <https://eprint.iacr.org/2019/266>.
//!
//! Adapted from the Apache 2.0+MIT licensed implementation originally from:
//! <https://github.com/taikoxyz/halo2curves/pull/2>
//! <https://github.com/privacy-scaling-explorations/halo2curves/pull/83>
//!
//! Copyright (c) 2023 Privacy Scaling Explorations Team

// TODO(tarcieri): optimized implementation for 32-bit platforms (#380)
// TODO(tarcieri): optimize using safegcd-bounds (#634)

#![allow(clippy::needless_range_loop)]

#[macro_use]
mod macros;

#[cfg(feature = "alloc")]
pub(crate) mod boxed;

use crate::{ConstChoice, ConstCtOption, Inverter, Limb, Odd, Uint, Word};
use subtle::CtOption;

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
pub struct SafeGcdInverter<const SAT_LIMBS: usize, const UNSAT_LIMBS: usize> {
    /// Modulus
    pub(super) modulus: UnsatInt<UNSAT_LIMBS>,

    /// Adjusting parameter (see toplevel documentation).
    adjuster: UnsatInt<UNSAT_LIMBS>,

    /// Multiplicative inverse of the modulus modulo 2^62
    inverse: i64,
}

/// Type of the Bernstein-Yang transition matrix multiplied by 2^62
type Matrix = [[i64; 2]; 2];

impl<const SAT_LIMBS: usize, const UNSAT_LIMBS: usize> SafeGcdInverter<SAT_LIMBS, UNSAT_LIMBS> {
    /// Creates the inverter for specified modulus and adjusting parameter.
    ///
    /// Modulus must be odd. Returns `None` if it is not.
    pub const fn new(modulus: &Odd<Uint<SAT_LIMBS>>, adjuster: &Uint<SAT_LIMBS>) -> Self {
        Self {
            modulus: UnsatInt::from_uint(&modulus.0),
            adjuster: UnsatInt::from_uint(adjuster),
            inverse: inv_mod2_62(modulus.0.as_words()),
        }
    }

    /// Returns either the adjusted modular multiplicative inverse for the argument or `None`
    /// depending on invertibility of the argument, i.e. its coprimality with the modulus
    pub const fn inv(&self, value: &Uint<SAT_LIMBS>) -> ConstCtOption<Uint<SAT_LIMBS>> {
        let (d, f) = divsteps(
            self.adjuster,
            self.modulus,
            UnsatInt::from_uint(value),
            self.inverse,
        );

        // At this point the absolute value of "f" equals the greatest common divisor of the
        // integer to be inverted and the modulus the inverter was created for.
        // Thus, if "f" is neither 1 nor -1, then the sought inverse does not exist.
        let antiunit = f.eq(&UnsatInt::MINUS_ONE);
        let ret = self.norm(d, antiunit);
        let is_some = f.eq(&UnsatInt::ONE).or(antiunit);
        ConstCtOption::new(ret.to_uint(), is_some)
    }

    /// Returns the greatest common divisor (GCD) of the two given numbers.
    ///
    /// This is defined on this type to piggyback on the definitions for `SAT_LIMBS` and
    /// `UNSAT_LIMBS` which are computed when defining `PrecomputeInverter::Inverter` for various
    /// `Uint` limb sizes.
    pub(crate) const fn gcd(f: &Uint<SAT_LIMBS>, g: &Uint<SAT_LIMBS>) -> Uint<SAT_LIMBS> {
        let inverse = inv_mod2_62(f.as_words());
        let e = UnsatInt::<UNSAT_LIMBS>::ONE;
        let f = UnsatInt::from_uint(f);
        let g = UnsatInt::from_uint(g);
        let (_, mut f) = divsteps(e, f, g, inverse);
        f = UnsatInt::select(&f, &f.neg(), f.is_negative());
        f.to_uint()
    }

    /// Returns the greatest common divisor (GCD) of the two given numbers.
    ///
    /// This version is variable-time with respect to `g`.
    pub(crate) const fn gcd_vartime(f: &Uint<SAT_LIMBS>, g: &Uint<SAT_LIMBS>) -> Uint<SAT_LIMBS> {
        let inverse = inv_mod2_62(f.as_words());
        let e = UnsatInt::<UNSAT_LIMBS>::ONE;
        let f = UnsatInt::from_uint(f);
        let g = UnsatInt::from_uint(g);
        let (_, mut f) = divsteps_vartime(e, f, g, inverse);
        f = UnsatInt::select(&f, &f.neg(), f.is_negative());
        f.to_uint()
    }

    /// Returns either "value (mod M)" or "-value (mod M)", where M is the modulus the inverter
    /// was created for, depending on "negate", which determines the presence of "-" in the used
    /// formula. The input integer lies in the interval (-2 * M, M).
    const fn norm(
        &self,
        mut value: UnsatInt<UNSAT_LIMBS>,
        negate: ConstChoice,
    ) -> UnsatInt<UNSAT_LIMBS> {
        value = UnsatInt::select(&value, &value.add(&self.modulus), value.is_negative());
        value = UnsatInt::select(&value, &value.neg(), negate);
        value = UnsatInt::select(&value, &value.add(&self.modulus), value.is_negative());
        value
    }
}

impl<const SAT_LIMBS: usize, const UNSAT_LIMBS: usize> Inverter
    for SafeGcdInverter<SAT_LIMBS, UNSAT_LIMBS>
{
    type Output = Uint<SAT_LIMBS>;

    fn invert(&self, value: &Uint<SAT_LIMBS>) -> CtOption<Self::Output> {
        self.inv(value).into()
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
const fn inv_mod2_62(value: &[Word]) -> i64 {
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
    (x.wrapping_mul(y.wrapping_add(1)) & (u64::MAX >> 2)) as i64
}

/// Algorithm `divsteps2` to compute (δₙ, fₙ, gₙ) = divstepⁿ(δ, f, g) as described in Figure 10.1
/// of <https://eprint.iacr.org/2019/266.pdf>.
///
/// This version runs in a fixed number of iterations relative to the highest bit of `f` or `g`
/// as described in Figure 11.1.
const fn divsteps<const LIMBS: usize>(
    mut e: UnsatInt<LIMBS>,
    f_0: UnsatInt<LIMBS>,
    mut g: UnsatInt<LIMBS>,
    inverse: i64,
) -> (UnsatInt<LIMBS>, UnsatInt<LIMBS>) {
    let mut d = UnsatInt::ZERO;
    let mut f = f_0;
    let mut delta = 1;
    let mut matrix;
    let mut i = 0;
    let m = iterations(f_0.bits(), g.bits());

    while i < m {
        (delta, matrix) = jump(&f.0, &g.0, delta);
        (f, g) = fg(f, g, matrix);
        (d, e) = de(&f_0, inverse, matrix, d, e);
        i += 1;
    }

    debug_assert!(g.eq(&UnsatInt::ZERO).to_bool_vartime());
    (d, f)
}

/// Algorithm `divsteps2` to compute (δₙ, fₙ, gₙ) = divstepⁿ(δ, f, g) as described in Figure 10.1
/// of <https://eprint.iacr.org/2019/266.pdf>.
///
/// This version is variable-time with respect to `g`.
const fn divsteps_vartime<const LIMBS: usize>(
    mut e: UnsatInt<LIMBS>,
    f_0: UnsatInt<LIMBS>,
    mut g: UnsatInt<LIMBS>,
    inverse: i64,
) -> (UnsatInt<LIMBS>, UnsatInt<LIMBS>) {
    let mut d = UnsatInt::ZERO;
    let mut f = f_0;
    let mut delta = 1;
    let mut matrix;

    while !g.eq(&UnsatInt::ZERO).to_bool_vartime() {
        (delta, matrix) = jump(&f.0, &g.0, delta);
        (f, g) = fg(f, g, matrix);
        (d, e) = de(&f_0, inverse, matrix, d, e);
    }

    (d, f)
}

/// Returns the Bernstein-Yang transition matrix multiplied by 2^62 and the new value of the
/// delta variable for the 62 basic steps of the Bernstein-Yang method, which are to be
/// performed sequentially for specified initial values of f, g and delta
const fn jump(f: &[u64], g: &[u64], mut delta: i64) -> (i64, Matrix) {
    // This function is defined because the method "min" of the i64 type is not constant
    const fn min(a: i64, b: i64) -> i64 {
        if a > b {
            b
        } else {
            a
        }
    }

    let (mut steps, mut f, mut g) = (62, f[0] as i64, g[0] as i128);
    let mut t: Matrix = [[1, 0], [0, 1]];

    loop {
        let zeros = min(steps, g.trailing_zeros() as i64);
        (steps, delta, g) = (steps - zeros, delta + zeros, g >> zeros);
        t[0] = [t[0][0] << zeros, t[0][1] << zeros];

        if steps == 0 {
            break;
        }
        if delta > 0 {
            (delta, f, g) = (-delta, g as i64, -f as i128);
            (t[0], t[1]) = (t[1], [-t[0][0], -t[0][1]]);
        }

        // The formula (3 * x) xor 28 = -1 / x (mod 32) for an odd integer x in the two's
        // complement code has been derived from the formula (3 * x) xor 2 = 1 / x (mod 32)
        // attributed to Peter Montgomery.
        let mask = (1 << min(min(steps, 1 - delta), 5)) - 1;
        let w = (g as i64).wrapping_mul(f.wrapping_mul(3) ^ 28) & mask;

        t[1] = [t[0][0] * w + t[1][0], t[0][1] * w + t[1][1]];
        g += w as i128 * f as i128;
    }

    (delta, t)
}

/// Returns the updated values of the variables f and g for specified initial ones and
/// Bernstein-Yang transition matrix multiplied by 2^62.
///
/// The returned vector is "matrix * (f, g)' / 2^62", where "'" is the transpose operator.
const fn fg<const LIMBS: usize>(
    f: UnsatInt<LIMBS>,
    g: UnsatInt<LIMBS>,
    t: Matrix,
) -> (UnsatInt<LIMBS>, UnsatInt<LIMBS>) {
    (
        f.mul(t[0][0]).add(&g.mul(t[0][1])).shr(),
        f.mul(t[1][0]).add(&g.mul(t[1][1])).shr(),
    )
}

/// Returns the updated values of the variables d and e for specified initial ones and
/// Bernstein-Yang transition matrix multiplied by 2^62.
///
/// The returned vector is congruent modulo M to "matrix * (d, e)' / 2^62 (mod M)", where M is the
/// modulus the inverter was created for and "'" stands for the transpose operator.
///
/// Both the input and output values lie in the interval (-2 * M, M).
const fn de<const LIMBS: usize>(
    modulus: &UnsatInt<LIMBS>,
    inverse: i64,
    t: Matrix,
    d: UnsatInt<LIMBS>,
    e: UnsatInt<LIMBS>,
) -> (UnsatInt<LIMBS>, UnsatInt<LIMBS>) {
    let mask = UnsatInt::<LIMBS>::MASK as i64;
    let mut md =
        t[0][0] * d.is_negative().to_u8() as i64 + t[0][1] * e.is_negative().to_u8() as i64;
    let mut me =
        t[1][0] * d.is_negative().to_u8() as i64 + t[1][1] * e.is_negative().to_u8() as i64;

    let cd = t[0][0]
        .wrapping_mul(d.lowest() as i64)
        .wrapping_add(t[0][1].wrapping_mul(e.lowest() as i64))
        & mask;

    let ce = t[1][0]
        .wrapping_mul(d.lowest() as i64)
        .wrapping_add(t[1][1].wrapping_mul(e.lowest() as i64))
        & mask;

    md -= (inverse.wrapping_mul(cd).wrapping_add(md)) & mask;
    me -= (inverse.wrapping_mul(ce).wrapping_add(me)) & mask;

    let cd = d.mul(t[0][0]).add(&e.mul(t[0][1])).add(&modulus.mul(md));
    let ce = d.mul(t[1][0]).add(&e.mul(t[1][1])).add(&modulus.mul(me));

    (cd.shr(), ce.shr())
}

/// Compute the number of iterations required to compute Bernstein-Yang on the two values.
///
/// Adapted from Fig 11.1 of <https://eprint.iacr.org/2019/266.pdf>
///
/// The paper proves that the algorithm will converge (i.e. `g` will be `0`) in all cases when
/// the algorithm runs this particular number of iterations.
///
/// Once `g` reaches `0`, continuing to run the algorithm will have no effect.
// TODO(tarcieri): improved bounds using https://github.com/sipa/safegcd-bounds
pub(crate) const fn iterations(f_bits: u32, g_bits: u32) -> usize {
    // Select max of `f_bits`, `g_bits`
    let d = ConstChoice::from_u32_lt(f_bits, g_bits).select_u32(f_bits, g_bits);
    let addend = ConstChoice::from_u32_lt(d, 46).select_u32(57, 80);
    ((49 * d + addend) / 17) as usize
}

/// "Bigint"-like (62 * LIMBS)-bit signed integer type, whose variables store numbers in the two's
/// complement code as arrays of 62-bit limbs in little endian order.
///
/// The arithmetic operations for this type are wrapping ones.
#[derive(Clone, Copy, Debug)]
pub(super) struct UnsatInt<const LIMBS: usize>(pub [u64; LIMBS]);

impl<const LIMBS: usize> UnsatInt<LIMBS> {
    /// Number of bits in each limb.
    pub const LIMB_BITS: usize = 62;

    /// Mask, in which the 62 lowest bits are 1.
    pub const MASK: u64 = u64::MAX >> (64 - Self::LIMB_BITS);

    /// Representation of -1.
    pub const MINUS_ONE: Self = Self([Self::MASK; LIMBS]);

    /// Representation of 0.
    pub const ZERO: Self = Self([0; LIMBS]);

    /// Representation of 1.
    pub const ONE: Self = {
        let mut ret = Self::ZERO;
        ret.0[0] = 1;
        ret
    };

    /// Convert from 32/64-bit saturated representation used by `Uint` to the 62-bit unsaturated
    /// representation used by `UnsatInt`.
    ///
    /// Returns a big unsigned integer as an array of 62-bit chunks, which is equal modulo
    /// 2 ^ (62 * S) to the input big unsigned integer stored as an array of 64-bit chunks.
    ///
    /// The ordering of the chunks in these arrays is little-endian.
    #[allow(trivial_numeric_casts)]
    pub const fn from_uint<const SAT_LIMBS: usize>(input: &Uint<SAT_LIMBS>) -> Self {
        if LIMBS != safegcd_nlimbs!(SAT_LIMBS * Limb::BITS as usize) {
            panic!("incorrect number of limbs");
        }

        let mut output = [0; LIMBS];
        impl_limb_convert!(Word, Word::BITS as usize, input.as_words(), u64, 62, output);

        Self(output)
    }

    /// Convert from 62-bit unsaturated representation used by `UnsatInt` to the 32/64-bit saturated
    /// representation used by `Uint`.
    ///
    /// Returns a big unsigned integer as an array of 32/64-bit chunks, which is equal modulo
    /// 2 ^ (64 * S) to the input big unsigned integer stored as an array of 62-bit chunks.
    ///
    /// The ordering of the chunks in these arrays is little-endian.
    #[allow(trivial_numeric_casts, clippy::wrong_self_convention)]
    pub const fn to_uint<const SAT_LIMBS: usize>(&self) -> Uint<SAT_LIMBS> {
        debug_assert!(
            !self.is_negative().to_bool_vartime(),
            "can't convert negative number to Uint"
        );

        if LIMBS != safegcd_nlimbs!(SAT_LIMBS * Limb::BITS as usize) {
            panic!("incorrect number of limbs");
        }

        let mut ret = [0 as Word; SAT_LIMBS];
        impl_limb_convert!(u64, 62, &self.0, Word, Word::BITS as usize, ret);
        Uint::from_words(ret)
    }

    /// Const fn equivalent for `Add::add`.
    pub const fn add(&self, other: &Self) -> Self {
        let (mut ret, mut carry) = (Self::ZERO, 0);
        let mut i = 0;

        while i < LIMBS {
            let sum = self.0[i] + other.0[i] + carry;
            ret.0[i] = sum & Self::MASK;
            carry = sum >> Self::LIMB_BITS;
            i += 1;
        }

        ret
    }

    /// Const fn equivalent for `Mul::<i64>::mul`.
    pub const fn mul(&self, other: i64) -> Self {
        let mut ret = Self::ZERO;
        // If the short multiplicand is non-negative, the standard multiplication algorithm is
        // performed. Otherwise, the product of the additively negated multiplicands is found as
        // follows.
        //
        // Since for the two's complement code the additive negation is the result of adding 1 to
        // the bitwise inverted argument's representation, for any encoded integers x and y we have
        // x * y = (-x) * (-y) = (!x + 1) * (-y) = !x * (-y) + (-y), where "!" is the bitwise
        // inversion and arithmetic operations are performed according to the rules of the code.
        //
        // If the short multiplicand is negative, the algorithm below uses this formula by
        // substituting the short multiplicand for y and turns into the modified standard
        // multiplication algorithm, where the carry flag is initialized with the additively
        // negated short multiplicand and the chunks of the long multiplicand are bitwise inverted.
        let (other, mut carry, mask) = if other < 0 {
            (-other, -other as u64, Self::MASK)
        } else {
            (other, 0, 0)
        };

        let mut i = 0;
        while i < LIMBS {
            let sum = (carry as u128) + ((self.0[i] ^ mask) as u128) * (other as u128);
            ret.0[i] = sum as u64 & Self::MASK;
            carry = (sum >> Self::LIMB_BITS) as u64;
            i += 1;
        }

        ret
    }

    /// Const fn equivalent for `Neg::neg`.
    pub const fn neg(&self) -> Self {
        // For the two's complement code the additive negation is the result of adding 1 to the
        // bitwise inverted argument's representation.
        let (mut ret, mut carry) = (Self::ZERO, 1);
        let mut i = 0;

        while i < LIMBS {
            let sum = (self.0[i] ^ Self::MASK) + carry;
            ret.0[i] = sum & Self::MASK;
            carry = sum >> Self::LIMB_BITS;
            i += 1;
        }

        ret
    }

    /// Returns the result of applying 62-bit right arithmetical shift to the current number.
    pub const fn shr(&self) -> Self {
        let mut ret = Self::ZERO;
        ret.0[LIMBS - 1] = self.is_negative().select_u64(ret.0[LIMBS - 1], Self::MASK);

        let mut i = 0;
        while i < LIMBS - 1 {
            ret.0[i] = self.0[i + 1];
            i += 1;
        }

        ret
    }

    /// Const fn equivalent for `PartialEq::eq`.
    pub const fn eq(&self, other: &Self) -> ConstChoice {
        let mut ret = ConstChoice::TRUE;
        let mut i = 0;

        while i < LIMBS {
            ret = ret.and(ConstChoice::from_u64_eq(self.0[i], other.0[i]));
            i += 1;
        }

        ret
    }

    /// Returns "true" iff the current number is negative.
    pub const fn is_negative(&self) -> ConstChoice {
        ConstChoice::from_u64_gt(self.0[LIMBS - 1], Self::MASK >> 1)
    }

    /// Returns the lowest 62 bits of the current number.
    pub const fn lowest(&self) -> u64 {
        self.0[0]
    }

    /// Select between two [`UnsatInt`] values in constant time.
    pub const fn select(a: &Self, b: &Self, choice: ConstChoice) -> Self {
        let mut ret = Self::ZERO;
        let mut i = 0;

        while i < LIMBS {
            ret.0[i] = choice.select_u64(a.0[i], b.0[i]);
            i += 1;
        }

        ret
    }

    /// Calculate the number of leading zeros in the binary representation of this number.
    pub const fn leading_zeros(&self) -> u32 {
        let mut count = 0;
        let mut i = LIMBS;
        let mut nonzero_limb_not_encountered = ConstChoice::TRUE;

        while i > 0 {
            i -= 1;
            let l = self.0[i];
            let z = l.leading_zeros() - 2;
            count += nonzero_limb_not_encountered.if_true_u32(z);
            nonzero_limb_not_encountered =
                nonzero_limb_not_encountered.and(ConstChoice::from_u64_nonzero(l).not());
        }

        count
    }

    /// Calculate the number of bits in this value (i.e. index of the highest bit) in constant time.
    pub const fn bits(&self) -> u32 {
        (LIMBS as u32 * 62) - self.leading_zeros()
    }
}

#[cfg(test)]
mod tests {
    use super::iterations;
    use crate::{Inverter, PrecomputeInverter, U256};

    type UnsatInt = super::UnsatInt<4>;

    impl<const LIMBS: usize> PartialEq for crate::modular::safegcd::UnsatInt<LIMBS> {
        fn eq(&self, other: &Self) -> bool {
            self.eq(other).to_bool_vartime()
        }
    }

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

    #[test]
    fn iterations_boundary_conditions() {
        assert_eq!(iterations(0, 0), 4);
        assert_eq!(iterations(0, 45), 134);
        assert_eq!(iterations(0, 46), 135);
    }

    #[test]
    fn unsatint_add() {
        assert_eq!(UnsatInt::ZERO, UnsatInt::ZERO.add(&UnsatInt::ZERO));
        assert_eq!(UnsatInt::ONE, UnsatInt::ONE.add(&UnsatInt::ZERO));
        assert_eq!(UnsatInt::ZERO, UnsatInt::MINUS_ONE.add(&UnsatInt::ONE));
    }

    #[test]
    fn unsatint_mul() {
        assert_eq!(UnsatInt::ZERO, UnsatInt::ZERO.mul(0));
        assert_eq!(UnsatInt::ZERO, UnsatInt::ZERO.mul(1));
        assert_eq!(UnsatInt::ZERO, UnsatInt::ONE.mul(0));
        assert_eq!(UnsatInt::ZERO, UnsatInt::MINUS_ONE.mul(0));
        assert_eq!(UnsatInt::ONE, UnsatInt::ONE.mul(1));
        assert_eq!(UnsatInt::MINUS_ONE, UnsatInt::MINUS_ONE.mul(1));
    }

    #[test]
    fn unsatint_neg() {
        assert_eq!(UnsatInt::ZERO, UnsatInt::ZERO.neg());
        assert_eq!(UnsatInt::MINUS_ONE, UnsatInt::ONE.neg());
        assert_eq!(UnsatInt::ONE, UnsatInt::MINUS_ONE.neg());
    }

    #[test]
    fn unsatint_is_negative() {
        assert!(!UnsatInt::ZERO.is_negative().to_bool_vartime());
        assert!(!UnsatInt::ONE.is_negative().to_bool_vartime());
        assert!(UnsatInt::MINUS_ONE.is_negative().to_bool_vartime());
    }

    #[test]
    fn unsatint_shr() {
        let n = super::UnsatInt([
            0,
            1211048314408256470,
            1344008336933394898,
            3913497193346473913,
            2764114971089162538,
            4,
        ]);

        assert_eq!(
            &n.shr().0,
            &[
                1211048314408256470,
                1344008336933394898,
                3913497193346473913,
                2764114971089162538,
                4,
                0
            ]
        );
    }
}
