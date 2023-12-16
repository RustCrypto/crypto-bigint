//! Implementation of Bernstein-Yang modular inversion and GCD algorithm as described in:
//! <https://eprint.iacr.org/2019/266>.
//!
//! Adapted from the Apache 2.0+MIT licensed implementation originally from:
//! <https://github.com/privacy-scaling-explorations/halo2curves/pull/83>
//!
//! Copyright (c) 2023 Privacy Scaling Explorations Team

// TODO(tarcieri): optimized implementation for 32-bit platforms (#380)

#![allow(clippy::needless_range_loop)]

use crate::{ConstChoice, Inverter, Limb, Uint, Word};
use subtle::CtOption;

/// Type of the modular multiplicative inverter based on the Bernstein-Yang method.
/// The inverter can be created for a specified modulus M and adjusting parameter A
/// to compute the adjusted multiplicative inverses of positive integers, i.e. for
/// computing (1 / x) * A (mod M) for a positive integer x.
///
/// The adjusting parameter allows computing the multiplicative inverses in the case of
/// using the Montgomery representation for the input or the expected output. If R is
/// the Montgomery factor, the multiplicative inverses in the appropriate representation
/// can be computed provided that the value of A is chosen as follows:
/// - A = 1, if both the input and the expected output are in the standard form
/// - A = R^2 mod M, if both the input and the expected output are in the Montgomery form
/// - A = R mod M, if either the input or the expected output is in the Montgomery form,
/// but not both of them
///
/// The public methods of this type receive and return unsigned big integers as arrays of
/// 64-bit chunks, the ordering of which is little-endian. Both the modulus and the integer
/// to be inverted should not exceed 2 ^ (62 * L - 64)
///
/// For better understanding the implementation, the following resources are recommended:
/// - D. Bernstein, B.-Y. Yang, "Fast constant-time gcd computation and modular inversion",
/// <https://gcd.cr.yp.to/safegcd-20190413.pdf>
/// - P. Wuille, "The safegcd implementation in libsecp256k1 explained",
/// <https://github.com/bitcoin-core/secp256k1/blob/master/doc/safegcd_implementation.md>
#[derive(Clone, Debug)]
pub struct BernsteinYangInverter<const SAT_LIMBS: usize, const UNSAT_LIMBS: usize> {
    /// Modulus
    pub(super) modulus: Uint62L<UNSAT_LIMBS>,

    /// Adjusting parameter
    adjuster: Uint62L<UNSAT_LIMBS>,

    /// Multiplicative inverse of the modulus modulo 2^62
    inverse: i64,
}

/// Type of the Bernstein-Yang transition matrix multiplied by 2^62
type Matrix = [[i64; 2]; 2];

impl<const SAT_LIMBS: usize, const UNSAT_LIMBS: usize>
    BernsteinYangInverter<SAT_LIMBS, UNSAT_LIMBS>
{
    /// Creates the inverter for specified modulus and adjusting parameter.
    ///
    /// Modulus must be odd. Returns `ConstChoice::FALSE` if it is not.
    #[allow(trivial_numeric_casts)]
    pub const fn new(modulus: &Uint<SAT_LIMBS>, adjuster: &Uint<SAT_LIMBS>) -> (Self, ConstChoice) {
        if UNSAT_LIMBS != bernstein_yang_nlimbs!(SAT_LIMBS * Limb::BITS as usize) {
            panic!("BernsteinYangInverter has incorrect number of limbs");
        }

        let ret = Self {
            modulus: Uint62L::<UNSAT_LIMBS>(sat_to_unsat::<UNSAT_LIMBS>(modulus.as_words())),
            adjuster: Uint62L::<UNSAT_LIMBS>(sat_to_unsat::<UNSAT_LIMBS>(adjuster.as_words())),
            inverse: inv_mod2_62(modulus.as_words()),
        };

        (ret, modulus.is_odd())
    }

    /// Returns either the adjusted modular multiplicative inverse for the argument or None
    /// depending on invertibility of the argument, i.e. its coprimality with the modulus
    pub const fn inv(&self, value: &Uint<SAT_LIMBS>) -> (Uint<SAT_LIMBS>, ConstChoice) {
        let (mut d, mut e) = (Uint62L::ZERO, self.adjuster);
        let mut g = Uint62L::<UNSAT_LIMBS>(sat_to_unsat::<UNSAT_LIMBS>(value.as_words()));
        let (mut delta, mut f) = (1, self.modulus);
        let mut matrix;

        while !g.eq(&Uint62L::ZERO) {
            (delta, matrix) = Self::jump(&f, &g, delta);
            (f, g) = Self::fg(f, g, matrix);
            (d, e) = self.de(d, e, matrix);
        }
        // At this point the absolute value of "f" equals the greatest common divisor
        // of the integer to be inverted and the modulus the inverter was created for.
        // Thus, if "f" is neither 1 nor -1, then the sought inverse does not exist
        let antiunit = f.eq(&Uint62L::MINUS_ONE);
        let words = unsat_to_sat::<SAT_LIMBS>(&self.norm(d, antiunit).0);
        let is_some = ConstChoice::from_word_lsb((f.eq(&Uint62L::ONE) || antiunit) as Word);
        (Uint::from_words(words), is_some)
    }

    /// Returns the Bernstein-Yang transition matrix multiplied by 2^62 and the new value
    /// of the delta variable for the 62 basic steps of the Bernstein-Yang method, which
    /// are to be performed sequentially for specified initial values of f, g and delta
    const fn jump(
        f: &Uint62L<UNSAT_LIMBS>,
        g: &Uint62L<UNSAT_LIMBS>,
        mut delta: i64,
    ) -> (i64, Matrix) {
        // This function is defined because the method "min" of the i64 type is not constant
        const fn min(a: i64, b: i64) -> i64 {
            if a > b {
                b
            } else {
                a
            }
        }

        let (mut steps, mut f, mut g) = (62, f.lowest() as i64, g.lowest() as i128);
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

            // The formula (3 * x) xor 28 = -1 / x (mod 32) for an odd integer x
            // in the two's complement code has been derived from the formula
            // (3 * x) xor 2 = 1 / x (mod 32) attributed to Peter Montgomery
            let mask = (1 << min(min(steps, 1 - delta), 5)) - 1;
            let w = (g as i64).wrapping_mul(f.wrapping_mul(3) ^ 28) & mask;

            t[1] = [t[0][0] * w + t[1][0], t[0][1] * w + t[1][1]];
            g += w as i128 * f as i128;
        }

        (delta, t)
    }

    /// Returns the updated values of the variables f and g for specified initial ones and Bernstein-Yang transition
    /// matrix multiplied by 2^62. The returned vector is "matrix * (f, g)' / 2^62", where "'" is the transpose operator
    const fn fg(
        f: Uint62L<UNSAT_LIMBS>,
        g: Uint62L<UNSAT_LIMBS>,
        t: Matrix,
    ) -> (Uint62L<UNSAT_LIMBS>, Uint62L<UNSAT_LIMBS>) {
        (
            f.mul(t[0][0]).add(&g.mul(t[0][1])).shift(),
            f.mul(t[1][0]).add(&g.mul(t[1][1])).shift(),
        )
    }

    /// Returns the updated values of the variables d and e for specified initial ones and Bernstein-Yang transition
    /// matrix multiplied by 2^62. The returned vector is congruent modulo M to "matrix * (d, e)' / 2^62 (mod M)",
    /// where M is the modulus the inverter was created for and "'" stands for the transpose operator. Both the input
    /// and output values lie in the interval (-2 * M, M)
    const fn de(
        &self,
        d: Uint62L<UNSAT_LIMBS>,
        e: Uint62L<UNSAT_LIMBS>,
        t: Matrix,
    ) -> (Uint62L<UNSAT_LIMBS>, Uint62L<UNSAT_LIMBS>) {
        let mask = Uint62L::<UNSAT_LIMBS>::MASK as i64;
        let mut md = t[0][0] * d.is_negative() as i64 + t[0][1] * e.is_negative() as i64;
        let mut me = t[1][0] * d.is_negative() as i64 + t[1][1] * e.is_negative() as i64;

        let cd = t[0][0]
            .wrapping_mul(d.lowest() as i64)
            .wrapping_add(t[0][1].wrapping_mul(e.lowest() as i64))
            & mask;
        let ce = t[1][0]
            .wrapping_mul(d.lowest() as i64)
            .wrapping_add(t[1][1].wrapping_mul(e.lowest() as i64))
            & mask;

        md -= (self.inverse.wrapping_mul(cd).wrapping_add(md)) & mask;
        me -= (self.inverse.wrapping_mul(ce).wrapping_add(me)) & mask;

        let cd = d
            .mul(t[0][0])
            .add(&e.mul(t[0][1]))
            .add(&self.modulus.mul(md));
        let ce = d
            .mul(t[1][0])
            .add(&e.mul(t[1][1]))
            .add(&self.modulus.mul(me));

        (cd.shift(), ce.shift())
    }

    /// Returns either "value (mod M)" or "-value (mod M)", where M is the modulus the
    /// inverter was created for, depending on "negate", which determines the presence
    /// of "-" in the used formula. The input integer lies in the interval (-2 * M, M)
    const fn norm(&self, mut value: Uint62L<UNSAT_LIMBS>, negate: bool) -> Uint62L<UNSAT_LIMBS> {
        if value.is_negative() {
            value = value.add(&self.modulus);
        }

        if negate {
            value = value.neg();
        }

        if value.is_negative() {
            value = value.add(&self.modulus);
        }

        value
    }
}

impl<const SAT_LIMBS: usize, const UNSAT_LIMBS: usize> Inverter
    for BernsteinYangInverter<SAT_LIMBS, UNSAT_LIMBS>
{
    type Output = Uint<SAT_LIMBS>;

    fn invert(&self, value: &Uint<SAT_LIMBS>) -> CtOption<Self::Output> {
        let (ret, choice) = self.inv(value);
        CtOption::new(ret, choice.into())
    }
}

/// Returns the multiplicative inverse of the argument modulo 2^62. The implementation is based
/// on the Hurchalla's method for computing the multiplicative inverse modulo a power of two.
/// For better understanding the implementation, the following paper is recommended:
/// J. Hurchalla, "An Improved Integer Multiplicative Inverse (modulo 2^w)",
/// https://arxiv.org/pdf/2204.04342.pdf
const fn inv_mod2_62(value: &[Word]) -> i64 {
    let value = {
        #[cfg(target_pointer_width = "32")]
        {
            debug_assert!(value.len() >= 2);
            value[0] as u64 | (value[1] as u64) << 32
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

/// Write an impl of a limb conversion function.
///
/// Workaround for making this function generic around limb types while still allowing it to be `const fn`.
macro_rules! impl_limb_convert {
    ($input_type:ty, $input_bits:expr, $output_type:ty, $output_bits:expr, $output_size:expr, $input:expr) => {{
        // This function is defined because the method "min" of the usize type is not constant
        const fn min(a: usize, b: usize) -> usize {
            if a > b {
                b
            } else {
                a
            }
        }

        let total = min($input.len() * $input_bits, $output_size * $output_bits);
        let mut output = [0 as $output_type; $output_size];
        let mut bits = 0;

        while bits < total {
            let (i, o) = (bits % $input_bits, bits % $output_bits);
            output[bits / $output_bits] |= ($input[bits / $input_bits] >> i) as $output_type << o;
            bits += min($input_bits - i, $output_bits - o);
        }

        let mask = (<$output_type>::MAX as $output_type) >> (<$output_type>::BITS as usize - $output_bits);
        let mut filled = total / $output_bits + if total % $output_bits > 0 { 1 } else { 0 };

        while filled > 0 {
            filled -= 1;
            output[filled] &= mask;
        }

        output
    }};
}

/// Convert from 64-bit saturated representation used by `Uint` to the 62-bit unsaturated representation used by
/// `Uint62`.
///
/// Returns a big unsigned integer as an array of 62-bit chunks, which is equal modulo 2 ^ (62 * S) to the input big
/// unsigned integer stored as an array of 64-bit chunks.
///
/// The ordering of the chunks in these arrays is little-endian.
#[allow(trivial_numeric_casts)]
const fn sat_to_unsat<const S: usize>(input: &[Word]) -> [u64; S] {
    impl_limb_convert!(Word, Word::BITS as usize, u64, 62, S, input)
}

/// Convert from 62-bit unsaturated representation used by `Uint62` to the 64-bit saturated representation used by
/// `Uint`.
///
/// Returns a big unsigned integer as an array of 64-bit chunks, which is equal modulo 2 ^ (64 * S) to the input big
/// unsigned integer stored as an array of 62-bit chunks.
///
/// The ordering of the chunks in these arrays is little-endian
#[allow(trivial_numeric_casts)]
const fn unsat_to_sat<const S: usize>(input: &[u64]) -> [Word; S] {
    impl_limb_convert!(u64, 62, Word, Word::BITS as usize, S, input)
}

/// `Uint`-like (62 * LIMBS)-bit integer type, whose variables store numbers in the two's complement code as arrays of
/// 62-bit limbs.
///
/// The ordering of the chunks in these arrays is little-endian.
///
/// The arithmetic operations for this type are wrapping ones.
#[derive(Clone, Copy, Debug)]
pub(super) struct Uint62L<const LIMBS: usize>(pub [u64; LIMBS]);

impl<const LIMBS: usize> Uint62L<LIMBS> {
    /// Number of bits in each limb.
    pub const LIMB_BITS: usize = 62;

    /// Mask, in which the B lowest bits are 1 and only they.
    pub const MASK: u64 = u64::MAX >> (64 - Self::LIMB_BITS);

    /// Representation of -1.
    pub const MINUS_ONE: Self = Self([Self::MASK; LIMBS]);

    /// Representation of 0.
    pub const ZERO: Self = Self([0; LIMBS]);

    /// Representation of 1.
    pub const ONE: Self = {
        let mut data = [0; LIMBS];
        data[0] = 1;
        Self(data)
    };

    /// Returns the result of applying 62-bit right arithmetical shift to the current number.
    pub const fn shift(&self) -> Self {
        let mut data = [0; LIMBS];
        if self.is_negative() {
            data[LIMBS - 1] = Self::MASK;
        }

        let mut i = 0;
        while i < LIMBS - 1 {
            data[i] = self.0[i + 1];
            i += 1;
        }

        Self(data)
    }

    /// Returns the lowest 62 bits of the current number.
    pub const fn lowest(&self) -> u64 {
        self.0[0]
    }

    /// Returns "true" iff the current number is negative.
    pub const fn is_negative(&self) -> bool {
        self.0[LIMBS - 1] > (Self::MASK >> 1)
    }

    /// Const fn equivalent for `PartialEq::eq`.
    pub const fn eq(&self, other: &Self) -> bool {
        let mut ret = true;
        let mut i = 0;

        while i < LIMBS {
            ret &= self.0[i] == other.0[i];
            i += 1;
        }

        ret
    }

    /// Const fn equivalent for `Add::add`.
    pub const fn add(&self, other: &Self) -> Self {
        let (mut data, mut carry) = ([0; LIMBS], 0);
        let mut i = 0;

        while i < LIMBS {
            let sum = self.0[i] + other.0[i] + carry;
            data[i] = sum & Self::MASK;
            carry = sum >> Self::LIMB_BITS;
            i += 1;
        }

        Self(data)
    }

    /// Const fn equivalent for `Neg::neg`.
    pub const fn neg(&self) -> Self {
        // For the two's complement code the additive negation is the result
        // of adding 1 to the bitwise inverted argument's representation
        let (mut data, mut carry) = ([0; LIMBS], 1);
        let mut i = 0;

        while i < LIMBS {
            let sum = (self.0[i] ^ Self::MASK) + carry;
            data[i] = sum & Self::MASK;
            carry = sum >> Self::LIMB_BITS;
            i += 1;
        }

        Self(data)
    }

    /// Const fn equivalent for `Mul::<i64>::mul`.
    pub const fn mul(&self, other: i64) -> Self {
        let mut data = [0; LIMBS];
        // If the short multiplicand is non-negative, the standard multiplication
        // algorithm is performed. Otherwise, the product of the additively negated
        // multiplicands is found as follows. Since for the two's complement code
        // the additive negation is the result of adding 1 to the bitwise inverted
        // argument's representation, for any encoded integers x and y we have
        // x * y = (-x) * (-y) = (!x + 1) * (-y) = !x * (-y) + (-y),  where "!" is
        // the bitwise inversion and arithmetic operations are performed according
        // to the rules of the code. If the short multiplicand is negative, the
        // algorithm below uses this formula by substituting the short multiplicand
        // for y and turns into the modified standard multiplication algorithm,
        // where the carry flag is initialized with the additively negated short
        // multiplicand and the chunks of the long multiplicand are bitwise inverted
        let (other, mut carry, mask) = if other < 0 {
            (-other, -other as u64, Self::MASK)
        } else {
            (other, 0, 0)
        };

        let mut i = 0;
        while i < LIMBS {
            let sum = (carry as u128) + ((self.0[i] ^ mask) as u128) * (other as u128);
            data[i] = sum as u64 & Self::MASK;
            carry = (sum >> Self::LIMB_BITS) as u64;
            i += 1;
        }

        Self(data)
    }
}
