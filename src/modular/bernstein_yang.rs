//! Implementation of Bernstein-Yang modular inversion and GCD algorithm as described in:
//! <https://eprint.iacr.org/2019/266>.
//!
//! Adapted from the Apache 2.0+MIT licensed implementation originally from:
//! <https://github.com/privacy-scaling-explorations/halo2curves/pull/83>
//!
//! Copyright (c) 2023 Privacy Scaling Explorations Team

// TODO(tarcieri): optimized implementation for 32-bit platforms (#380)

#![allow(clippy::needless_range_loop)]

use crate::Word;

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
#[derive(Debug)]
pub struct BernsteinYangInverter<const L: usize> {
    /// Modulus
    modulus: CInt<62, L>,

    /// Adjusting parameter
    adjuster: CInt<62, L>,

    /// Multiplicative inverse of the modulus modulo 2^62
    inverse: i64,
}

/// Type of the Bernstein-Yang transition matrix multiplied by 2^62
type Matrix = [[i64; 2]; 2];

impl<const L: usize> BernsteinYangInverter<L> {
    /// Creates the inverter for specified modulus and adjusting parameter
    #[allow(trivial_numeric_casts)]
    pub const fn new(modulus: &[Word], adjuster: &[Word]) -> Self {
        Self {
            modulus: CInt::<62, L>(convert_in::<{ Word::BITS as usize }, 62, L>(modulus)),
            adjuster: CInt::<62, L>(convert_in::<{ Word::BITS as usize }, 62, L>(adjuster)),
            inverse: inv_mod62(modulus),
        }
    }

    /// Returns either the adjusted modular multiplicative inverse for the argument or None
    /// depending on invertibility of the argument, i.e. its coprimality with the modulus
    pub const fn invert<const S: usize>(&self, value: &[Word]) -> Option<[Word; S]> {
        let (mut d, mut e) = (CInt::ZERO, self.adjuster);
        let mut g = CInt::<62, L>(convert_in::<{ Word::BITS as usize }, 62, L>(value));
        let (mut delta, mut f) = (1, self.modulus);
        let mut matrix;

        while !g.eq(&CInt::ZERO) {
            (delta, matrix) = Self::jump(&f, &g, delta);
            (f, g) = Self::fg(f, g, matrix);
            (d, e) = self.de(d, e, matrix);
        }
        // At this point the absolute value of "f" equals the greatest common divisor
        // of the integer to be inverted and the modulus the inverter was created for.
        // Thus, if "f" is neither 1 nor -1, then the sought inverse does not exist
        let antiunit = f.eq(&CInt::MINUS_ONE);
        if !f.eq(&CInt::ONE) && !antiunit {
            return None;
        }
        Some(convert_out::<62, { Word::BITS as usize }, S>(
            &self.norm(d, antiunit).0,
        ))
    }

    /// Returns the Bernstein-Yang transition matrix multiplied by 2^62 and the new value
    /// of the delta variable for the 62 basic steps of the Bernstein-Yang method, which
    /// are to be performed sequentially for specified initial values of f, g and delta
    const fn jump(f: &CInt<62, L>, g: &CInt<62, L>, mut delta: i64) -> (i64, Matrix) {
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
    const fn fg(f: CInt<62, L>, g: CInt<62, L>, t: Matrix) -> (CInt<62, L>, CInt<62, L>) {
        (
            f.mul(t[0][0]).add(&g.mul(t[0][1])).shift(),
            f.mul(t[1][0]).add(&g.mul(t[1][1])).shift(),
        )
    }

    /// Returns the updated values of the variables d and e for specified initial ones and Bernstein-Yang transition
    /// matrix multiplied by 2^62. The returned vector is congruent modulo M to "matrix * (d, e)' / 2^62 (mod M)",
    /// where M is the modulus the inverter was created for and "'" stands for the transpose operator. Both the input
    /// and output values lie in the interval (-2 * M, M)
    const fn de(&self, d: CInt<62, L>, e: CInt<62, L>, t: Matrix) -> (CInt<62, L>, CInt<62, L>) {
        let mask = CInt::<62, L>::MASK as i64;
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
    const fn norm(&self, mut value: CInt<62, L>, negate: bool) -> CInt<62, L> {
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

/// Returns the multiplicative inverse of the argument modulo 2^62. The implementation is based
/// on the Hurchalla's method for computing the multiplicative inverse modulo a power of two.
/// For better understanding the implementation, the following paper is recommended:
/// J. Hurchalla, "An Improved Integer Multiplicative Inverse (modulo 2^w)",
/// https://arxiv.org/pdf/2204.04342.pdf
const fn inv_mod62(value: &[Word]) -> i64 {
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

/// Write an impl of a `convert_*` function.
///
/// Workaround for making this function generic while still allowing it to be `const fn`.
macro_rules! impl_convert {
    ($input_type:ty, $output_type:ty, $input:expr) => {{
        // This function is defined because the method "min" of the usize type is not constant
        const fn min(a: usize, b: usize) -> usize {
            if a > b {
                b
            } else {
                a
            }
        }

        let total = min($input.len() * I, S * O);
        let mut output = [0 as $output_type; S];
        let mut bits = 0;

        while bits < total {
            let (i, o) = (bits % I, bits % O);
            output[bits / O] |= ($input[bits / I] >> i) as $output_type << o;
            bits += min(I - i, O - o);
        }

        let mask = (<$output_type>::MAX as $output_type) >> (<$output_type>::BITS as usize - O);
        let mut filled = total / O + if total % O > 0 { 1 } else { 0 };

        while filled > 0 {
            filled -= 1;
            output[filled] &= mask;
        }

        output
    }};
}

/// Returns a big unsigned integer as an array of O-bit chunks, which is equal modulo
/// 2 ^ (O * S) to the input big unsigned integer stored as an array of I-bit chunks.
/// The ordering of the chunks in these arrays is little-endian
#[allow(trivial_numeric_casts)]
const fn convert_in<const I: usize, const O: usize, const S: usize>(input: &[Word]) -> [u64; S] {
    impl_convert!(Word, u64, input)
}

/// Returns a big unsigned integer as an array of O-bit chunks, which is equal modulo
/// 2 ^ (O * S) to the input big unsigned integer stored as an array of I-bit chunks.
/// The ordering of the chunks in these arrays is little-endian
#[allow(trivial_numeric_casts)]
const fn convert_out<const I: usize, const O: usize, const S: usize>(input: &[u64]) -> [Word; S] {
    impl_convert!(u64, Word, input)
}

/// Big signed (B * L)-bit integer type, whose variables store
/// numbers in the two's complement code as arrays of B-bit chunks.
/// The ordering of the chunks in these arrays is little-endian.
/// The arithmetic operations for this type are wrapping ones.
#[derive(Clone, Copy, Debug)]
struct CInt<const B: usize, const L: usize>(pub [u64; L]);

impl<const B: usize, const L: usize> CInt<B, L> {
    /// Mask, in which the B lowest bits are 1 and only they
    pub const MASK: u64 = u64::MAX >> (64 - B);

    /// Representation of -1
    pub const MINUS_ONE: Self = Self([Self::MASK; L]);

    /// Representation of 0
    pub const ZERO: Self = Self([0; L]);

    /// Representation of 1
    pub const ONE: Self = {
        let mut data = [0; L];
        data[0] = 1;
        Self(data)
    };

    /// Returns the result of applying B-bit right
    /// arithmetical shift to the current number
    pub const fn shift(&self) -> Self {
        let mut data = [0; L];
        if self.is_negative() {
            data[L - 1] = Self::MASK;
        }

        let mut i = 0;
        while i < L - 1 {
            data[i] = self.0[i + 1];
            i += 1;
        }

        Self(data)
    }

    /// Returns the lowest B bits of the current number
    pub const fn lowest(&self) -> u64 {
        self.0[0]
    }

    /// Returns "true" iff the current number is negative
    pub const fn is_negative(&self) -> bool {
        self.0[L - 1] > (Self::MASK >> 1)
    }

    /// Const fn equivalent for `PartialEq::eq`
    pub const fn eq(&self, other: &Self) -> bool {
        let mut ret = true;
        let mut i = 0;

        while i < L {
            ret &= self.0[i] == other.0[i];
            i += 1;
        }

        ret
    }

    /// Const fn equivalent for `Add::add`
    pub const fn add(&self, other: &Self) -> Self {
        let (mut data, mut carry) = ([0; L], 0);
        let mut i = 0;

        while i < L {
            let sum = self.0[i] + other.0[i] + carry;
            data[i] = sum & CInt::<B, L>::MASK;
            carry = sum >> B;
            i += 1;
        }

        Self(data)
    }

    /// Const fn equivalent for `Neg::neg`
    pub const fn neg(&self) -> Self {
        // For the two's complement code the additive negation is the result
        // of adding 1 to the bitwise inverted argument's representation
        let (mut data, mut carry) = ([0; L], 1);
        let mut i = 0;

        while i < L {
            let sum = (self.0[i] ^ Self::MASK) + carry;
            data[i] = sum & Self::MASK;
            carry = sum >> B;
            i += 1;
        }

        Self(data)
    }

    /// Const fn equivalent for `Mul::<i64>::mul`
    pub const fn mul(&self, other: i64) -> Self {
        let mut data = [0; L];
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
        while i < L {
            let sum = (carry as u128) + ((self.0[i] ^ mask) as u128) * (other as u128);
            data[i] = sum as u64 & Self::MASK;
            carry = (sum >> B) as u64;
            i += 1;
        }

        Self(data)
    }
}
