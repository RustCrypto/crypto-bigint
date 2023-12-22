//! Implementation of Bernstein-Yang modular inversion and GCD algorithm as described in:
//! <https://eprint.iacr.org/2019/266>.
//!
//! See parent module for more information.

use super::{inv_mod2_62, jump, Matrix};
use crate::{BoxedUint, Inverter, Limb, Odd, Word};
use alloc::{boxed::Box, vec::Vec};
use subtle::{Choice, ConstantTimeEq, CtOption};

/// Modular multiplicative inverter based on the Bernstein-Yang method.
///
/// See [`super::BernsteinYangInverter`] for more information.
#[derive(Clone, Debug)]
pub struct BoxedBernsteinYangInverter {
    /// Modulus
    pub(crate) modulus: BoxedInt62L,

    /// Adjusting parameter (see toplevel documentation).
    adjuster: BoxedInt62L,

    /// Multiplicative inverse of the modulus modulo 2^62
    inverse: i64,
}

impl BoxedBernsteinYangInverter {
    /// Creates the inverter for specified modulus and adjusting parameter.
    ///
    /// Modulus must be odd. Returns `None` if it is not.
    pub fn new(modulus: &Odd<BoxedUint>, adjuster: &BoxedUint) -> Self {
        Self {
            modulus: BoxedInt62L::from(&modulus.0),
            adjuster: BoxedInt62L::from(&adjuster.widen(modulus.bits_precision())),
            inverse: inv_mod2_62(modulus.0.as_words()),
        }
    }

    /// Returns either "value (mod M)" or "-value (mod M)", where M is the modulus the inverter
    /// was created for, depending on "negate", which determines the presence of "-" in the used
    /// formula. The input integer lies in the interval (-2 * M, M).
    fn norm(&self, mut value: BoxedInt62L, negate: bool) -> BoxedInt62L {
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

    fn invert(&self, value: &BoxedUint) -> CtOption<Self::Output> {
        let mut d = BoxedInt62L::zero(self.modulus.0.len());
        let mut e = self.adjuster.clone();
        let mut f = self.modulus.clone();
        let mut g = BoxedInt62L::from(value).widen(d.0.len());

        debug_assert_eq!(g.0.len(), self.modulus.0.len());

        let mut delta = 1;
        let mut matrix;

        while !g.is_zero() {
            (delta, matrix) = jump(&f.0, &g.0, delta);
            (f, g) = fg(f, g, matrix);
            (d, e) = de(&self.modulus, self.inverse, d, e, matrix);
        }
        // At this point the absolute value of "f" equals the greatest common divisor of the
        // integer to be inverted and the modulus the inverter was created for.
        // Thus, if "f" is neither 1 nor -1, then the sought inverse does not exist.
        let antiunit = f.is_minus_one();
        let ret = self.norm(d, antiunit);
        let is_some = Choice::from(f.is_one() as u8) | Choice::from(antiunit as u8);

        CtOption::new(ret.to_uint(value.bits_precision()), is_some)
    }
}

/// Returns the updated values of the variables f and g for specified initial ones and
/// Bernstein-Yang transition matrix multiplied by 2^62. The returned vector is
/// "matrix * (f, g)' / 2^62", where "'" is the transpose operator.
fn fg(f: BoxedInt62L, g: BoxedInt62L, t: Matrix) -> (BoxedInt62L, BoxedInt62L) {
    (
        f.mul(t[0][0]).add(&g.mul(t[0][1])).shr(),
        f.mul(t[1][0]).add(&g.mul(t[1][1])).shr(),
    )
}

/// Returns the updated values of the variables d and e for specified initial ones and
/// Bernstein-Yang transition matrix multiplied by 2^62. The returned vector is congruent modulo
/// M to "matrix * (d, e)' / 2^62 (mod M)", where M is the modulus the inverter was created for
/// and "'" stands for the transpose operator. Both the input and output values lie in the
/// interval (-2 * M, M).
fn de(
    modulus: &BoxedInt62L,
    inverse: i64,
    d: BoxedInt62L,
    e: BoxedInt62L,
    t: Matrix,
) -> (BoxedInt62L, BoxedInt62L) {
    let mask = BoxedInt62L::MASK as i64;
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

    md -= (inverse.wrapping_mul(cd).wrapping_add(md)) & mask;
    me -= (inverse.wrapping_mul(ce).wrapping_add(me)) & mask;

    let cd = d.mul(t[0][0]).add(&e.mul(t[0][1])).add(&modulus.mul(md));
    let ce = d.mul(t[1][0]).add(&e.mul(t[1][1])).add(&modulus.mul(me));

    (cd.shr(), ce.shr())
}

/// "Bigint"-like (62 * LIMBS)-bit signed integer type, whose variables store numbers in the two's
/// complement code as arrays of 62-bit limbs in little endian order.
///
/// The arithmetic operations for this type are wrapping ones.
#[derive(Clone, Debug)]
pub(crate) struct BoxedInt62L(Box<[u64]>);

/// Convert from 64-bit saturated representation used by `Uint` to the 62-bit unsaturated
/// representation used by `BoxedInt62L`.
///
/// Returns a big unsigned integer as an array of 62-bit chunks, which is equal modulo
/// 2 ^ (62 * S) to the input big unsigned integer stored as an array of 64-bit chunks.
///
/// The ordering of the chunks in these arrays is little-endian.
impl From<&BoxedUint> for BoxedInt62L {
    #[allow(trivial_numeric_casts)]
    fn from(input: &BoxedUint) -> BoxedInt62L {
        let saturated_nlimbs = if Word::BITS == 32 && input.nlimbs() == 1 {
            2
        } else {
            input.nlimbs()
        };

        let nlimbs = bernstein_yang_nlimbs!(saturated_nlimbs * Limb::BITS as usize);

        // Workaround for 32-bit platforms: if the input is a single limb, it will be smaller input
        // than is usable for Bernstein-Yang with is currently natively 64-bits on all targets
        let mut tmp: [Word; 2] = [0; 2];

        let input = if Word::BITS == 32 && input.nlimbs() == 1 {
            tmp[0] = input.limbs[0].0;
            &tmp
        } else {
            input.as_words()
        };

        let mut output = vec![0u64; nlimbs];
        impl_limb_convert!(Word, Word::BITS as usize, input, u64, 62, output);
        Self(output.into())
    }
}

impl BoxedInt62L {
    /// Number of bits in each limb.
    pub const LIMB_BITS: usize = 62;

    /// Mask, in which the 62 lowest bits are 1.
    pub const MASK: u64 = u64::MAX >> (64 - Self::LIMB_BITS);

    /// Convert to a `BoxedUint` of the given precision.
    #[allow(trivial_numeric_casts)]
    fn to_uint(&self, mut bits_precision: u32) -> BoxedUint {
        // The current Bernstein-Yang implementation is natively 64-bit on all targets
        if bits_precision == 32 {
            bits_precision = 64;
        }

        debug_assert_eq!(
            self.0.len(),
            bernstein_yang_nlimbs!(bits_precision as usize)
        );
        assert!(
            !self.is_negative(),
            "can't convert negative number to BoxedUint"
        );

        let mut ret = BoxedUint {
            limbs: vec![Limb::ZERO; nlimbs!(bits_precision)].into(),
        };

        impl_limb_convert!(
            u64,
            62,
            &self.0,
            Word,
            Word::BITS as usize,
            ret.as_words_mut()
        );

        ret
    }

    /// Add.
    #[must_use]
    pub fn add(&self, other: &Self) -> Self {
        let nlimbs = self.0.len();
        debug_assert_eq!(nlimbs, other.0.len());

        let mut ret = Self::zero(nlimbs);
        let mut carry = 0;
        let mut i = 0;

        while i < nlimbs {
            let sum = self.0[i] + other.0[i] + carry;
            ret.0[i] = sum & Self::MASK;
            carry = sum >> Self::LIMB_BITS;
            i += 1;
        }

        ret
    }

    /// Mul.
    #[must_use]
    pub fn mul(&self, other: i64) -> Self {
        let nlimbs = self.0.len();
        let mut ret = Self::zero(nlimbs);

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
        while i < nlimbs {
            let sum = (carry as u128) + ((self.0[i] ^ mask) as u128) * (other as u128);
            ret.0[i] = sum as u64 & Self::MASK;
            carry = (sum >> Self::LIMB_BITS) as u64;
            i += 1;
        }

        ret
    }

    /// Negate.
    #[must_use]
    pub fn neg(&self) -> Self {
        // For the two's complement code the additive negation is the result of adding 1 to the
        // bitwise inverted argument's representation.
        let nlimbs = self.0.len();
        let mut ret = Self::zero(nlimbs);
        let mut carry = 1;
        let mut i = 0;

        while i < nlimbs {
            let sum = (self.0[i] ^ Self::MASK) + carry;
            ret.0[i] = sum & Self::MASK;
            carry = sum >> Self::LIMB_BITS;
            i += 1;
        }

        ret
    }

    /// Returns the result of applying 62-bit right arithmetical shift to the current number.
    #[must_use]
    pub fn shr(&self) -> Self {
        let nlimbs = self.0.len();
        let mut ret = Self::zero(nlimbs);

        if self.is_negative() {
            ret.0[nlimbs - 1] = Self::MASK;
        }

        let mut i = 0;
        while i < nlimbs - 1 {
            ret.0[i] = self.0[i + 1];
            i += 1;
        }

        ret
    }

    /// Get the value zero for the given number of limbs.
    pub fn zero(nlimbs: usize) -> Self {
        Self(vec![0; nlimbs].into())
    }

    /// Widen self to the given number of limbs.
    pub fn widen(self, nlimbs: usize) -> Self {
        let mut limbs = Vec::from(self.0);
        debug_assert!(nlimbs >= limbs.len());
        limbs.truncate(nlimbs);
        Self(limbs.into())
    }

    /// Is the current value -1?
    pub fn is_minus_one(&self) -> bool {
        self.0
            .iter()
            .fold(true, |acc, &limb| acc & (limb == Self::MASK))
    }

    /// Returns "true" iff the current number is negative.
    pub fn is_negative(&self) -> bool {
        self.0[self.0.len() - 1] > (Self::MASK >> 1)
    }

    /// Is the current value zero?
    pub fn is_zero(&self) -> bool {
        self.0.iter().fold(true, |acc, &limb| acc & (limb == 0))
    }

    /// Is the current value one?
    pub fn is_one(&self) -> bool {
        self.0[1..]
            .iter()
            .fold(self.lowest() == 1, |acc, &limb| acc & (limb == 0))
    }

    /// Returns the lowest 62 bits of the current number.
    pub fn lowest(&self) -> u64 {
        self.0[0]
    }
}

impl PartialEq for BoxedInt62L {
    fn eq(&self, other: &Self) -> bool {
        self.0.ct_eq(&other.0).into()
    }
}

#[cfg(test)]
mod tests {
    use super::BoxedInt62L;
    use crate::{modular::bernstein_yang::Int62L, BoxedUint, Inverter, PrecomputeInverter, U256};
    use proptest::prelude::*;

    #[test]
    fn invert() {
        let g = BoxedUint::from_be_hex(
            "00000000CBF9350842F498CE441FC2DC23C7BF47D3DE91C327B2157C5E4EED77",
            256,
        )
        .unwrap();
        let modulus = BoxedUint::from_be_hex(
            "FFFFFFFF00000000FFFFFFFFFFFFFFFFBCE6FAADA7179E84F3B9CAC2FC632551",
            256,
        )
        .unwrap()
        .to_odd()
        .unwrap();
        let inverter = modulus.precompute_inverter();
        let result = inverter.invert(&g).unwrap();
        assert_eq!(
            BoxedUint::from_be_hex(
                "FB668F8F509790BC549B077098918604283D42901C92981062EB48BC723F617B",
                256
            )
            .unwrap(),
            result
        );
    }

    #[test]
    fn de() {
        let modulus = BoxedInt62L(
            vec![
                3727233105432618321,
                3718823987352861203,
                4611686018427387899,
                4611685743549481023,
                255,
                0,
            ]
            .into(),
        );
        let inverse = 3687945983376704433;
        let d = BoxedInt62L(
            vec![
                3490544662636853909,
                2211268325417683828,
                992023446686701852,
                4539270294123539695,
                4611686018427387762,
                4611686018427387903,
            ]
            .into(),
        );
        let e = BoxedInt62L(
            vec![
                4004071259428196451,
                1262234674432503659,
                4060414504149367846,
                1804121722707079191,
                4611686018427387712,
                4611686018427387903,
            ]
            .into(),
        );
        let t = [[-45035996273704960, 409827566090715136], [-14, 25]];

        let (new_d, new_e) = super::de(&modulus, inverse, d, e, t);
        assert_eq!(
            new_d,
            BoxedInt62L(
                vec![
                    1211048314408256470,
                    1344008336933394898,
                    3913497193346473913,
                    2764114971089162538,
                    4,
                    0,
                ]
                .into()
            )
        );

        assert_eq!(new_e, BoxedInt62L(vec![0, 0, 0, 0, 0, 0].into()));
    }

    #[test]
    fn boxed_int62l_is_zero() {
        let zero = BoxedInt62L::from(&U256::ZERO.into());
        assert!(zero.is_zero());

        let one = BoxedInt62L::from(&U256::ONE.into());
        assert!(!one.is_zero());
    }

    #[test]
    fn boxed_int62l_is_one() {
        let zero = BoxedInt62L::from(&U256::ZERO.into());
        assert!(!zero.is_one());

        let one = BoxedInt62L::from(&U256::ONE.into());
        assert!(one.is_one());
    }

    #[test]
    fn int62l_shr() {
        let n = BoxedInt62L(
            vec![
                0,
                1211048314408256470,
                1344008336933394898,
                3913497193346473913,
                2764114971089162538,
                4,
            ]
            .into(),
        );

        assert_eq!(
            &*n.shr().0,
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

    prop_compose! {
        fn u256()(bytes in any::<[u8; 32]>()) -> U256 {
            U256::from_le_slice(&bytes)
        }
    }

    proptest! {
        #[test]
        fn boxed_int62l_add(x in u256(), y in u256()) {
            let x_ref = Int62L::<{ bernstein_yang_nlimbs!(256usize) }>::from_uint(&x);
            let y_ref = Int62L::<{ bernstein_yang_nlimbs!(256usize) }>::from_uint(&y);
            let x_boxed = BoxedInt62L::from(&x.into());
            let y_boxed = BoxedInt62L::from(&y.into());

            let expected = x_ref.add(&y_ref);
            let actual = x_boxed.add(&y_boxed);
            prop_assert_eq!(&expected.0, &*actual.0);
        }

        #[test]
        fn boxed_int62l_mul(x in u256(), y in any::<i64>()) {
            let x_ref = Int62L::<{ bernstein_yang_nlimbs!(256usize) }>::from_uint(&x);
            let x_boxed = BoxedInt62L::from(&x.into());

            let expected = x_ref.mul(y);
            let actual = x_boxed.mul(y);
            prop_assert_eq!(&expected.0, &*actual.0);
        }

        #[test]
        fn boxed_int62l_neg(x in u256()) {
            let x_ref = Int62L::<{ bernstein_yang_nlimbs!(256usize) }>::from_uint(&x);
            let x_boxed = BoxedInt62L::from(&x.into());

            let expected = x_ref.neg();
            let actual = x_boxed.neg();
            prop_assert_eq!(&expected.0, &*actual.0);
        }

        #[test]
        fn boxed_int62l_shr(x in u256()) {
            let x_ref = Int62L::<{ bernstein_yang_nlimbs!(256usize) }>::from_uint(&x);
            let x_boxed = BoxedInt62L::from(&x.into());

            let expected = x_ref.shr();
            let actual = x_boxed.shr();
            prop_assert_eq!(&expected.0, &*actual.0);
        }

        #[test]
        fn boxed_int62l_is_negative(x in u256()) {
            let x_ref = Int62L::<{ bernstein_yang_nlimbs!(256usize) }>::from_uint(&x);
            let x_boxed = BoxedInt62L::from(&x.into());
            assert_eq!(x_ref.is_negative(), x_boxed.is_negative());
        }

        #[test]
        fn boxed_int62l_is_minus_one(x in u256()) {
            let x_ref = Int62L::<{ bernstein_yang_nlimbs!(256usize) }>::from_uint(&x);
            let x_boxed = BoxedInt62L::from(&x.into());
            assert_eq!(x_ref.eq(&Int62L::MINUS_ONE), x_boxed.is_minus_one());
        }
    }
}
