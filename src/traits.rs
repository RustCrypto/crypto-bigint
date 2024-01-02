//! Traits provided by this crate

mod sealed;

pub use num_traits::{
    WrappingAdd, WrappingMul, WrappingNeg, WrappingShl, WrappingShr, WrappingSub,
};

pub(crate) use sealed::PrecomputeInverterWithAdjuster;

use crate::{Limb, NonZero};
use core::fmt::Debug;
use core::ops::{
    Add, BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Div, DivAssign, Mul, Not,
    Rem, Shl, ShlAssign, Shr, ShrAssign, Sub,
};
use subtle::{
    Choice, ConditionallySelectable, ConstantTimeEq, ConstantTimeGreater, ConstantTimeLess,
    CtOption,
};

#[cfg(feature = "rand_core")]
use rand_core::CryptoRngCore;

/// Integers whose representation takes a bounded amount of space.
pub trait Bounded {
    /// Size of this integer in bits.
    const BITS: u32;

    /// Size of this integer in bytes.
    const BYTES: usize;
}

/// Integer trait: represents common functionality of integer types provided by this crate.
pub trait Integer:
    'static
    + Add<Output = Self>
    + for<'a> Add<&'a Self, Output = Self>
    + AddMod<Output = Self>
    + AsRef<[Limb]>
    + BitAnd<Output = Self>
    + for<'a> BitAnd<&'a Self, Output = Self>
    + BitAndAssign
    + for<'a> BitAndAssign<&'a Self>
    + BitOr<Output = Self>
    + for<'a> BitOr<&'a Self, Output = Self>
    + BitOrAssign
    + for<'a> BitOrAssign<&'a Self>
    + BitXor<Output = Self>
    + for<'a> BitXor<&'a Self, Output = Self>
    + BitXorAssign
    + for<'a> BitXorAssign<&'a Self>
    + CheckedAdd
    + CheckedSub
    + CheckedMul
    + CheckedDiv
    + Clone
    // + ConditionallySelectable (see dalek-cryptography/subtle#94)
    + ConstantTimeEq
    + ConstantTimeGreater
    + ConstantTimeLess
    + Debug
    + Default
    + Div<NonZero<Self>, Output = Self>
    + for<'a> Div<&'a NonZero<Self>, Output = Self>
    + DivAssign<NonZero<Self>>
    + for<'a> DivAssign<&'a NonZero<Self>>
    + Eq
    + From<u8>
    + From<u16>
    + From<u32>
    + From<u64>
    + Mul<Output = Self>
    + for<'a> Mul<&'a Self, Output = Self>
    + MulMod<Output = Self>
    + NegMod<Output = Self>
    + Not<Output = Self>
    + Ord
    + Rem<NonZero<Self>, Output = Self>
    + for<'a> Rem<&'a NonZero<Self>, Output = Self>
    + Send
    + Sized
    + Shl<u32, Output = Self>
    + ShlAssign<u32>
    + Shr<u32, Output = Self>
    + ShrAssign<u32>
    + Sub<Output = Self>
    + for<'a> Sub<&'a Self, Output = Self>
    + SubMod<Output = Self>
    + Sync
    + WrappingAdd
    + WrappingSub
    + WrappingMul
    + WrappingNeg
    + WrappingShl
    + WrappingShr
    + Zero
{
    /// The value `1`.
    fn one() -> Self;

    /// Calculate the number of bits required to represent a given number.
    fn bits(&self) -> u32;

    /// Calculate the number of bits required to represent a given number in variable-time with
    /// respect to `self`.
    fn bits_vartime(&self) -> u32;

    /// Precision of this integer in bits.
    fn bits_precision(&self) -> u32;

    /// Precision of this integer in bytes.
    fn bytes_precision(&self) -> usize;

    /// Calculate the number of leading zeros in the binary representation of this number.
    fn leading_zeros(&self) -> u32  {
        self.bits_precision() - self.bits()
    }

    /// Number of limbs in this integer.
    fn nlimbs(&self) -> usize;

    /// Is this integer value an odd number?
    ///
    /// # Returns
    ///
    /// If odd, returns `Choice(1)`. Otherwise, returns `Choice(0)`.
    fn is_odd(&self) -> Choice {
        self.as_ref()
            .first()
            .map(|limb| limb.is_odd())
            .unwrap_or_else(|| Choice::from(0))
    }

    /// Is this integer value an even number?
    ///
    /// # Returns
    ///
    /// If even, returns `Choice(1)`. Otherwise, returns `Choice(0)`.
    fn is_even(&self) -> Choice {
        !self.is_odd()
    }
}

/// Fixed-width integers.
pub trait FixedInteger: Bounded + ConditionallySelectable + Constants + Copy + Integer {
    /// The number of limbs used on this platform.
    const LIMBS: usize;
}

/// Obtain a precomputed inverter for efficiently computing modular inversions for a given modulus.
pub trait PrecomputeInverter {
    /// Inverter type for integers of this size.
    type Inverter: Inverter<Output = Self::Output> + Sized;

    /// Output produced by the inverter.
    type Output;

    /// Obtain a precomputed inverter for `&self` as the modulus, using `Self::one()` as an adjusting parameter.
    ///
    /// Returns `None` if `self` is even.
    fn precompute_inverter(&self) -> Self::Inverter;
}

/// Trait impl'd by precomputed modular inverters.
pub trait Inverter {
    /// Output of an inversion.
    type Output;

    /// Compute a modular inversion, returning `None` if the result is undefined (i.e. if `value` is zero or isn't
    /// prime relative to the modulus).
    fn invert(&self, value: &Self::Output) -> CtOption<Self::Output>;
}

/// Zero values.
pub trait Zero: ConstantTimeEq + Sized {
    /// The value `0`.
    fn zero() -> Self;

    /// Determine if this value is equal to zero.
    ///
    /// # Returns
    ///
    /// If zero, returns `Choice(1)`. Otherwise, returns `Choice(0)`.
    #[inline]
    fn is_zero(&self) -> Choice {
        self.ct_eq(&Self::zero())
    }

    /// Set `self` to its additive identity, i.e. `Self::zero`.
    #[inline]
    fn set_zero(&mut self) {
        *self = Zero::zero();
    }
}

/// Trait for associating a constant representing zero.
///
/// Types which impl this trait automatically receive a blanket impl of [`Zero`].
pub trait ZeroConstant: Zero {
    /// The value `0`.
    const ZERO: Self;
}

impl<T: ZeroConstant> Zero for T {
    #[inline(always)]
    fn zero() -> T {
        Self::ZERO
    }
}

/// Trait for associating constant values with a type.
pub trait Constants: ZeroConstant {
    /// The value `1`.
    const ONE: Self;

    /// Maximum value this integer can express.
    const MAX: Self;
}

/// Random number generation support.
#[cfg(feature = "rand_core")]
pub trait Random: Sized {
    /// Generate a cryptographically secure random value.
    fn random(rng: &mut impl CryptoRngCore) -> Self;
}

/// Modular random number generation support.
#[cfg(feature = "rand_core")]
pub trait RandomMod: Sized + Zero {
    /// Generate a cryptographically secure random number which is less than
    /// a given `modulus`.
    ///
    /// This function uses rejection sampling, a method which produces an
    /// unbiased distribution of in-range values provided the underlying
    /// CSRNG is unbiased, but runs in variable-time.
    ///
    /// The variable-time nature of the algorithm should not pose a security
    /// issue so long as the underlying random number generator is truly a
    /// CSRNG, where previous outputs are unrelated to subsequent
    /// outputs and do not reveal information about the RNG's internal state.
    fn random_mod(rng: &mut impl CryptoRngCore, modulus: &NonZero<Self>) -> Self;
}

/// Compute `self + rhs mod p`.
pub trait AddMod<Rhs = Self> {
    /// Output type.
    type Output;

    /// Compute `self + rhs mod p`.
    ///
    /// Assumes `self` and `rhs` are `< p`.
    fn add_mod(&self, rhs: &Rhs, p: &Self) -> Self::Output;
}

/// Compute `self - rhs mod p`.
pub trait SubMod<Rhs = Self> {
    /// Output type.
    type Output;

    /// Compute `self - rhs mod p`.
    ///
    /// Assumes `self` and `rhs` are `< p`.
    fn sub_mod(&self, rhs: &Rhs, p: &Self) -> Self::Output;
}

/// Compute `-self mod p`.
pub trait NegMod {
    /// Output type.
    type Output;

    /// Compute `-self mod p`.
    #[must_use]
    fn neg_mod(&self, p: &Self) -> Self::Output;
}

/// Compute `self * rhs mod p`.
pub trait MulMod<Rhs = Self> {
    /// Output type.
    type Output;

    /// Compute `self * rhs mod p`.
    fn mul_mod(&self, rhs: &Rhs, p: &Self) -> Self::Output;
}

/// Checked addition.
pub trait CheckedAdd<Rhs = Self>: Sized {
    /// Perform checked addition, returning a [`CtOption`] which `is_some` only if the operation
    /// did not overflow.
    fn checked_add(&self, rhs: &Rhs) -> CtOption<Self>;
}

/// Checked division.
pub trait CheckedDiv<Rhs = Self>: Sized {
    /// Perform checked division, returning a [`CtOption`] which `is_some` only if the divisor is
    /// non-zero.
    fn checked_div(&self, rhs: &Rhs) -> CtOption<Self>;
}

/// Checked multiplication.
pub trait CheckedMul<Rhs = Self>: Sized {
    /// Perform checked multiplication, returning a [`CtOption`] which `is_some`
    /// only if the operation did not overflow.
    fn checked_mul(&self, rhs: &Rhs) -> CtOption<Self>;
}

/// Checked subtraction.
pub trait CheckedSub<Rhs = Self>: Sized {
    /// Perform checked subtraction, returning a [`CtOption`] which `is_some`
    /// only if the operation did not underflow.
    fn checked_sub(&self, rhs: &Rhs) -> CtOption<Self>;
}

/// Concatenate two numbers into a "wide" double-width value, using the `lo`
/// value as the least significant value.
pub trait Concat: ConcatMixed<Self, MixedOutput = Self::Output> {
    /// Concatenated output: twice the width of `Self`.
    type Output: Integer;

    /// Concatenate the two halves, with `self` as most significant and `lo`
    /// as the least significant.
    fn concat(&self, lo: &Self) -> Self::Output {
        self.concat_mixed(lo)
    }
}

/// Concatenate two numbers into a "wide" combined-width value, using the `lo`
/// value as the least significant value.
pub trait ConcatMixed<Lo: ?Sized = Self> {
    /// Concatenated output: combination of `Lo` and `Self`.
    type MixedOutput: Integer;

    /// Concatenate the two values, with `self` as most significant and `lo`
    /// as the least significant.
    fn concat_mixed(&self, lo: &Lo) -> Self::MixedOutput;
}

/// Split a number in half, returning the most significant half followed by
/// the least significant.
pub trait Split: SplitMixed<Self::Output, Self::Output> {
    /// Split output: high/low components of the value.
    type Output;

    /// Split this number in half, returning its high and low components
    /// respectively.
    fn split(&self) -> (Self::Output, Self::Output) {
        self.split_mixed()
    }
}

/// Split a number into parts, returning the most significant part followed by
/// the least significant.
pub trait SplitMixed<Hi, Lo> {
    /// Split this number into parts, returning its high and low components
    /// respectively.
    fn split_mixed(&self) -> (Hi, Lo);
}

/// Encoding support.
pub trait Encoding: Sized {
    /// Byte array representation.
    type Repr: AsRef<[u8]>
        + AsMut<[u8]>
        + Copy
        + Clone
        + Sized
        + for<'a> TryFrom<&'a [u8], Error = core::array::TryFromSliceError>;

    /// Decode from big endian bytes.
    fn from_be_bytes(bytes: Self::Repr) -> Self;

    /// Decode from little endian bytes.
    fn from_le_bytes(bytes: Self::Repr) -> Self;

    /// Encode to big endian bytes.
    fn to_be_bytes(&self) -> Self::Repr;

    /// Encode to little endian bytes.
    fn to_le_bytes(&self) -> Self::Repr;
}

/// Support for optimized squaring
pub trait Square: Sized
where
    for<'a> &'a Self: Mul<&'a Self, Output = Self>,
{
    /// Computes the same as `self.mul(self)`, but may be more efficient.
    fn square(&self) -> Self {
        self * self
    }
}

/// Constant-time exponentiation.
pub trait Pow<Exponent> {
    /// Raises to the `exponent` power.
    fn pow(&self, exponent: &Exponent) -> Self;
}

impl<T: PowBoundedExp<Exponent>, Exponent: Bounded> Pow<Exponent> for T {
    fn pow(&self, exponent: &Exponent) -> Self {
        self.pow_bounded_exp(exponent, Exponent::BITS)
    }
}

/// Constant-time exponentiation with exponent of a bounded bit size.
pub trait PowBoundedExp<Exponent> {
    /// Raises to the `exponent` power,
    /// with `exponent_bits` representing the number of (least significant) bits
    /// to take into account for the exponent.
    ///
    /// NOTE: `exponent_bits` may be leaked in the time pattern.
    fn pow_bounded_exp(&self, exponent: &Exponent, exponent_bits: u32) -> Self;
}

/// Performs modular multi-exponentiation using Montgomery's ladder.
///
/// See: Straus, E. G. Problems and solutions: Addition chains of vectors. American Mathematical Monthly 71 (1964), 806–808.
pub trait MultiExponentiate<Exponent, BasesAndExponents>: Pow<Exponent> + Sized
where
    BasesAndExponents: AsRef<[(Self, Exponent)]> + ?Sized,
{
    /// Calculates `x1 ^ k1 * ... * xn ^ kn`.
    fn multi_exponentiate(bases_and_exponents: &BasesAndExponents) -> Self;
}

impl<T, Exponent, BasesAndExponents> MultiExponentiate<Exponent, BasesAndExponents> for T
where
    T: MultiExponentiateBoundedExp<Exponent, BasesAndExponents>,
    Exponent: Bounded,
    BasesAndExponents: AsRef<[(Self, Exponent)]> + ?Sized,
{
    fn multi_exponentiate(bases_and_exponents: &BasesAndExponents) -> Self {
        Self::multi_exponentiate_bounded_exp(bases_and_exponents, Exponent::BITS)
    }
}

/// Performs modular multi-exponentiation using Montgomery's ladder.
/// `exponent_bits` represents the number of bits to take into account for the exponent.
///
/// See: Straus, E. G. Problems and solutions: Addition chains of vectors. American Mathematical Monthly 71 (1964), 806–808.
///
/// NOTE: this value is leaked in the time pattern.
pub trait MultiExponentiateBoundedExp<Exponent, BasesAndExponents>: Pow<Exponent> + Sized
where
    BasesAndExponents: AsRef<[(Self, Exponent)]> + ?Sized,
{
    /// Calculates `x1 ^ k1 * ... * xn ^ kn`.
    fn multi_exponentiate_bounded_exp(
        bases_and_exponents: &BasesAndExponents,
        exponent_bits: u32,
    ) -> Self;
}

/// Constant-time inversion.
pub trait Invert: Sized {
    /// Output of the inversion.
    type Output;

    /// Computes the inverse.
    fn invert(&self) -> Self::Output;
}

/// Widening multiply: returns a value with a number of limbs equal to the sum of the inputs.
pub trait WideningMul<Rhs = Self>: Sized {
    /// Output of the widening multiplication.
    type Output: Integer;

    /// Perform widening multiplication.
    fn widening_mul(&self, rhs: Rhs) -> Self::Output;
}
