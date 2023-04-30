//! Wrapping arithmetic.

use crate::Zero;
use core::fmt;
use subtle::{Choice, ConditionallySelectable, ConstantTimeEq};

#[cfg(feature = "num-traits")]
use num_traits::{Num};
#[cfg(feature = "num-traits")]
use core::ops::{Div, Rem, Mul, Add, Sub};
#[cfg(feature = "num-traits")]
use crate::{Integer, NonZero};

#[cfg(feature = "rand_core")]
use {crate::Random, rand_core::CryptoRngCore};

#[cfg(feature = "serde")]
use serdect::serde::{Deserialize, Deserializer, Serialize, Serializer};

/// Provides intentionally-wrapped arithmetic on `T`.
///
/// This is analogous to [`core::num::Wrapping`] but allows this crate to
/// define trait impls for this type.
#[derive(Copy, Clone, Debug, Default, Eq, PartialEq, PartialOrd, Ord)]
pub struct Wrapping<T>(pub T);

impl<T: Zero> Zero for Wrapping<T> {
    const ZERO: Self = Self(T::ZERO);
}

impl<T: fmt::Display> fmt::Display for Wrapping<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}

impl<T: fmt::Binary> fmt::Binary for Wrapping<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}

impl<T: fmt::Octal> fmt::Octal for Wrapping<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}

impl<T: fmt::LowerHex> fmt::LowerHex for Wrapping<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}

impl<T: fmt::UpperHex> fmt::UpperHex for Wrapping<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}

impl<T: ConditionallySelectable> ConditionallySelectable for Wrapping<T> {
    fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
        Wrapping(T::conditional_select(&a.0, &b.0, choice))
    }
}

impl<T: ConstantTimeEq> ConstantTimeEq for Wrapping<T> {
    fn ct_eq(&self, other: &Self) -> Choice {
        self.0.ct_eq(&other.0)
    }
}

#[cfg(feature = "num-traits")]
impl<T: Zero> num_traits::Zero for Wrapping<T>
    where Wrapping<T>:
    Add<Wrapping<T>, Output = Wrapping<T>>
    + PartialEq<Wrapping<T>>
{
    fn zero() -> Self {
        Self::ZERO
    }

    fn is_zero(&self) -> bool { self == &Self::ZERO }
}

#[cfg(feature = "num-traits")]
impl<T: Integer> num_traits::One for Wrapping<T>
    where Wrapping<T>:
    Add<Wrapping<T>, Output = Wrapping<T>>
    + Mul<Wrapping<T>, Output = Wrapping<T>>
{
    fn one() -> Self {
        Wrapping(T::ONE)
    }
}

#[cfg(feature = "num-traits")]
impl<T: Zero> Div<Wrapping<T>> for Wrapping<T>
    where Wrapping<T>: Div<NonZero<T>, Output = Wrapping<T>>
{
    type Output = Wrapping<T>;

    fn div(self, rhs: Wrapping<T>) -> Self::Output {
        self / NonZero::new(rhs.0).unwrap()
    }
}

#[cfg(feature = "num-traits")]
impl<T: Zero> Rem<Wrapping<T>> for Wrapping<T>
    where Wrapping<T>: Rem<NonZero<T>, Output = Wrapping<T>>
{
    type Output = Wrapping<T>;

    fn rem(self, rhs: Wrapping<T>) -> Self::Output {
        self % NonZero::new(rhs.0).unwrap()
    }
}

#[cfg(feature = "num-traits")]
impl<T: Integer + Zero> Num for Wrapping<T>
    where Wrapping<T>:
    Add<Wrapping<T>, Output = Wrapping<T>>
    + Sub<Wrapping<T>, Output = Wrapping<T>>
    + Mul<Wrapping<T>, Output = Wrapping<T>>
    + Div<NonZero<T>, Output = Wrapping<T>>
    + Rem<NonZero<T>, Output = Wrapping<T>>
{
    type FromStrRadixErr = ();

    fn from_str_radix(str: &str, radix: u32) -> Result<Self, Self::FromStrRadixErr> {
        todo!()
    }
}

#[cfg(feature = "rand_core")]
impl<T: Random> Random for Wrapping<T> {
    fn random(rng: &mut impl CryptoRngCore) -> Self {
        Wrapping(Random::random(rng))
    }
}

#[cfg(feature = "serde")]
impl<'de, T: Deserialize<'de>> Deserialize<'de> for Wrapping<T> {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        Ok(Self(T::deserialize(deserializer)?))
    }
}

#[cfg(feature = "serde")]
impl<T: Serialize> Serialize for Wrapping<T> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        self.0.serialize(serializer)
    }
}

#[cfg(all(test, feature = "num-traits"))]
mod tests {
    use num_traits::{Num, NumOps, Zero, One};
    use core::ops::{Div, Rem, Mul, Add, Sub};
    use crate::{Integer, NonZero};

    use crate::{Wrapping, U64};

    fn assures_num<T: Num>(x: T) {}

    #[test]
    fn num_traits() {
        const TEST: Wrapping<U64> = Wrapping(U64::from_u64(0x0011223344556677));

        assures_num(TEST)
    }
}

#[cfg(all(test, feature = "serde"))]
mod tests {
    use crate::{Wrapping, U64};

    #[test]
    fn serde() {
        const TEST: Wrapping<U64> = Wrapping(U64::from_u64(0x0011223344556677));

        let serialized = bincode::serialize(&TEST).unwrap();
        let deserialized: Wrapping<U64> = bincode::deserialize(&serialized).unwrap();

        assert_eq!(TEST, deserialized);
    }

    #[test]
    fn serde_owned() {
        const TEST: Wrapping<U64> = Wrapping(U64::from_u64(0x0011223344556677));

        let serialized = bincode::serialize(&TEST).unwrap();
        let deserialized: Wrapping<U64> = bincode::deserialize_from(serialized.as_slice()).unwrap();

        assert_eq!(TEST, deserialized);
    }
}
