//! Boxed implementation of Bernstein-Yang inversions.
// TODO(tarcieri): DRY out with the stack-allocated implementation when `const_mut_refs` is stable.

use super::{inv_mod2_62, Matrix};
use crate::{BoxedUint, Integer, Inverter, Limb, Word};
use alloc::boxed::Box;
use subtle::{Choice, ConstantTimeEq, CtOption};

/// Modular multiplicative inverter based on the Bernstein-Yang method with support for boxed integers.
///
/// See [`super::BernsteinYangInverter`] for a more detailed description.
#[derive(Clone, Debug)]
pub struct BoxedBernsteinYangInverter {
    /// Modulus
    pub(crate) modulus: BoxedUint62L,

    /// Adjusting parameter
    adjuster: BoxedUint62L,

    /// Multiplicative inverse of the modulus modulo 2^62
    inverse: i64,
}

impl BoxedBernsteinYangInverter {
    /// Creates the inverter for specified modulus and adjusting parameter.
    ///
    /// Modulus must be odd. Returns `None` if it is not.
    pub fn new(modulus: &BoxedUint, adjuster: &BoxedUint) -> CtOption<Self> {
        let ret = Self {
            modulus: modulus.into(),
            adjuster: adjuster.into(),
            inverse: inv_mod2_62(modulus.as_words()),
        };

        CtOption::new(ret, modulus.is_odd())
    }

    /// Returns the Bernstein-Yang transition matrix multiplied by 2^62 and the new value
    /// of the delta variable for the 62 basic steps of the Bernstein-Yang method, which
    /// are to be performed sequentially for specified initial values of f, g and delta
    fn jump(f: &BoxedUint62L, g: &BoxedUint62L, mut delta: i64) -> (i64, Matrix) {
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
    fn fg(f: &mut BoxedUint62L, g: &mut BoxedUint62L, t: Matrix) {
        // TODO(tarcieri): reduce allocations
        let f2 = f.mul(t[0][0]).add(&g.mul(t[0][1])).shr();
        let g2 = f.mul(t[1][0]).add(&g.mul(t[1][1])).shr();
        *f = f2;
        *g = g2;
    }

    /// Returns the updated values of the variables d and e for specified initial ones and Bernstein-Yang transition
    /// matrix multiplied by 2^62. The returned vector is congruent modulo M to "matrix * (d, e)' / 2^62 (mod M)",
    /// where M is the modulus the inverter was created for and "'" stands for the transpose operator. Both the input
    /// and output values lie in the interval (-2 * M, M)
    fn de(&self, d: &mut BoxedUint62L, e: &mut BoxedUint62L, t: Matrix) {
        let mask = BoxedUint62L::MASK as i64;
        let mut md = t[0][0] * d.is_negative() as i64 + t[0][1] * e.is_negative() as i64;
        let mut me = t[1][0] * d.is_negative() as i64 + t[1][1] * e.is_negative() as i64;

        // TODO(tarcieri): reduce allocations
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

        *d = cd.shr();
        *e = ce.shr();
    }

    /// Returns either "value (mod M)" or "-value (mod M)", where M is the modulus the
    /// inverter was created for, depending on "negate", which determines the presence
    /// of "-" in the used formula. The input integer lies in the interval (-2 * M, M)
    fn norm(&self, mut value: BoxedUint62L, negate: bool) -> BoxedUint62L {
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

impl Inverter for BoxedBernsteinYangInverter {
    type Output = BoxedUint;

    /// Returns either the adjusted modular multiplicative inverse for the argument or `None`
    /// depending on invertibility of the argument, i.e. its coprimality with the modulus
    fn invert(&self, value: &BoxedUint) -> CtOption<BoxedUint> {
        // Ensure `d` has the right number of limbs for `value`, but is initialized to `0`.
        let mut d = BoxedUint62L::from(value);
        d.0.iter_mut().for_each(|limb| *limb = 0);

        let mut e = self.adjuster.clone();
        let mut g = BoxedUint62L::from(value);
        let mut delta = 1;
        let mut f = self.modulus.clone();
        let mut matrix;

        while !g.is_zero() {
            (delta, matrix) = Self::jump(&f, &g, delta);
            Self::fg(&mut f, &mut g, matrix);
            self.de(&mut d, &mut e, matrix);
        }
        // At this point the absolute value of "f" equals the greatest common divisor
        // of the integer to be inverted and the modulus the inverter was created for.
        // Thus, if "f" is neither 1 nor -1, then the sought inverse does not exist
        let antiunit = f.is_minus_one();
        let ret = self.norm(d, antiunit);
        let is_some = Choice::from((f.is_one() || antiunit) as u8);

        let ret = BoxedUint::from(&ret);
        CtOption::new(ret.shorten(value.bits_precision()), is_some)
    }
}

/// `Uint`-like (62 * LIMBS)-bit integer type, whose variables store numbers in the two's complement code as arrays of
/// 62-bit limbs.
///
/// The ordering of the chunks in these arrays is little-endian.
///
/// The arithmetic operations for this type are wrapping ones.
#[derive(Clone, Debug)]
pub(crate) struct BoxedUint62L(pub Box<[u64]>);

impl BoxedUint62L {
    /// Number of bits in each limb.
    pub const LIMB_BITS: usize = 62;

    /// Mask, in which the 62 lowest bits are 1.
    pub const MASK: u64 = u64::MAX >> (64 - Self::LIMB_BITS);

    /// Addition.
    pub fn add(&self, other: &Self) -> Self {
        debug_assert_eq!(self.nlimbs(), other.nlimbs());
        let (mut ret, mut carry) = (self.clone(), 0);
        let mut i = 0;

        while i < ret.nlimbs() {
            let sum = self.0[i] + other.0[i] + carry;
            ret.0[i] = sum & Self::MASK;
            carry = sum >> Self::LIMB_BITS;
            i += 1;
        }

        ret
    }

    /// Multiplication by a short `i64` multiplicand.
    pub fn mul(&self, other: i64) -> Self {
        let mut ret = self.clone();

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
        while i < ret.nlimbs() {
            let sum = (carry as u128) + ((self.0[i] ^ mask) as u128) * (other as u128);
            ret.0[i] = sum as u64 & Self::MASK;
            carry = (sum >> Self::LIMB_BITS) as u64;
            i += 1;
        }

        ret
    }

    /// Negation.
    pub fn neg(&self) -> Self {
        // For the two's complement code the additive negation is the result
        // of adding 1 to the bitwise inverted argument's representation
        let (mut ret, mut carry) = (self.clone(), 1);
        let mut i = 0;

        while i < ret.nlimbs() {
            let sum = (self.0[i] ^ Self::MASK) + carry;
            ret.0[i] = sum & Self::MASK;
            carry = sum >> Self::LIMB_BITS;
            i += 1;
        }

        ret
    }

    /// Bitwise right shift.
    pub fn shr(&self) -> Self {
        let mut ret = self.clone();

        if self.is_negative() {
            ret.0[ret.nlimbs() - 1] = Self::MASK;
        }

        let mut i = 0;
        while i < ret.nlimbs() - 1 {
            ret.0[i] = self.0[i + 1];
            i += 1;
        }

        ret
    }

    /// Returns "true" iff the current number is negative.
    pub fn is_negative(&self) -> bool {
        self.0[self.nlimbs() - 1] > (Self::MASK >> 1)
    }

    /// Is this number equal to zero?
    pub fn is_zero(&self) -> bool {
        let mut ret = true;

        for &limb in &*self.0 {
            ret &= limb == 0;
        }

        ret
    }

    /// Is this number equal to one?
    pub fn is_one(&self) -> bool {
        let mut ret;
        let mut limbs = self.0.iter();

        if let Some(&limb) = limbs.next() {
            ret = limb == 1;
        } else {
            ret = false;
        }

        for &limb in limbs {
            ret &= limb == 0;
        }

        ret
    }

    /// Is this number equal to minus one?
    pub fn is_minus_one(&self) -> bool {
        let mut ret = true;

        for &limb in &*self.0 {
            ret &= limb == Self::MASK;
        }

        ret
    }

    /// Returns the lowest 62 bits of the current number.
    pub fn lowest(&self) -> u64 {
        self.0[0]
    }

    /// Get the number of limbs in this big integer.
    #[inline]
    pub fn nlimbs(&self) -> usize {
        self.0.len()
    }
}

impl ConstantTimeEq for BoxedUint62L {
    #[inline]
    fn ct_eq(&self, other: &Self) -> Choice {
        debug_assert_eq!(self.nlimbs(), other.nlimbs());
        let mut ret = Choice::from(1u8);

        for i in 0..self.nlimbs() {
            let a = &self.0[i];
            let b = &other.0[i];
            ret &= a.ct_eq(b);
        }

        ret
    }
}

impl From<&BoxedUint> for BoxedUint62L {
    /// Convert from 64-bit saturated representation used by `BoxedUint` to the 62-bit unsaturated
    /// representation used by `BoxedUint62L`.
    ///
    /// Returns a big unsigned integer as an array of 62-bit chunks, which is equal modulo
    /// 2 ^ (62 * S) to the input big unsigned integer stored as an array of 64-bit chunks.
    ///
    /// The ordering of the chunks in these arrays is little-endian.
    #[allow(trivial_numeric_casts)]
    fn from(input: &BoxedUint) -> Self {
        let unsat_limbs = bernstein_yang_nlimbs!(input.nlimbs() * Limb::BITS as usize);
        let mut ret = vec![0; unsat_limbs];
        impl_limb_convert!(Word, Word::BITS as usize, input.as_words(), u64, 62, ret);
        Self(ret.into())
    }
}

impl From<&BoxedUint62L> for BoxedUint {
    /// Convert from 62-bit unsaturated representation used by `Uint62` to the 64-bit saturated representation used by
    /// `Uint`.
    ///
    /// Returns a big unsigned integer as an array of 64-bit chunks, which is equal modulo 2 ^ (64 * S) to the input big
    /// unsigned integer stored as an array of 62-bit chunks.
    ///
    /// The ordering of the chunks in these arrays is little-endian
    #[allow(trivial_numeric_casts)]
    fn from(input: &BoxedUint62L) -> BoxedUint {
        let bits = input.0.len() * BoxedUint62L::LIMB_BITS;
        let mut limbs = vec![0; bits / Word::BITS as usize];
        impl_limb_convert!(u64, 62, &input.0, Word, Word::BITS as usize, limbs);
        BoxedUint::from_words(limbs)
    }
}
