//! Checked arithmetic.

use crate::{CheckedAdd, CheckedDiv, CheckedMul, CheckedSub, Choice, CtEq, CtOption, CtSelect};
use core::ops::{Add, Div, Mul, Sub};

#[cfg(feature = "serde")]
use serdect::serde::{Deserialize, Deserializer, Serialize, Serializer};

/// Provides intentionally-checked arithmetic on `T`.
///
/// Internally this leverages the [`CtOption`] type from the [`ctutils`] crate in order to
/// handle overflows.
#[derive(Copy, Clone, Debug)]
pub struct Checked<T>(pub CtOption<T>);

impl<T> Checked<T> {
    /// Create a new checked arithmetic wrapper for the given value.
    pub const fn new(val: T) -> Self {
        Self(CtOption::some(val))
    }
}

impl<T> Add<Self> for Checked<T>
where
    T: CheckedAdd + CtSelect + Default,
{
    type Output = Checked<T>;

    #[inline]
    fn add(self, rhs: Self) -> Self::Output {
        Checked(
            self.0
                .as_ref()
                .and_then(|lhs| rhs.0.as_ref().and_then(|rhs| lhs.checked_add(rhs))),
        )
    }
}

impl<T> Add<&Self> for Checked<T>
where
    T: CheckedAdd + CtSelect + Default,
{
    type Output = Checked<T>;

    #[inline]
    fn add(self, rhs: &Self) -> Self::Output {
        Checked(
            self.0
                .as_ref()
                .and_then(|lhs| rhs.0.as_ref().and_then(|rhs| lhs.checked_add(rhs))),
        )
    }
}

impl<T> Add<Checked<T>> for &Checked<T>
where
    T: CheckedAdd + CtSelect + Default,
{
    type Output = Checked<T>;

    #[inline]
    fn add(self, rhs: Checked<T>) -> Self::Output {
        Checked(
            self.0
                .as_ref()
                .and_then(|lhs| rhs.0.as_ref().and_then(|rhs| lhs.checked_add(rhs))),
        )
    }
}

impl<T> Add<&Checked<T>> for &Checked<T>
where
    T: CheckedAdd + CtSelect + Default,
{
    type Output = Checked<T>;

    #[inline]
    fn add(self, rhs: &Checked<T>) -> Self::Output {
        Checked(
            self.0
                .as_ref()
                .and_then(|lhs| rhs.0.as_ref().and_then(|rhs| lhs.checked_add(rhs))),
        )
    }
}

impl<T> Sub<Self> for Checked<T>
where
    T: CheckedSub + CtSelect + Default,
{
    type Output = Checked<T>;

    #[inline]
    fn sub(self, rhs: Self) -> Self::Output {
        Checked(
            self.0
                .as_ref()
                .and_then(|lhs| rhs.0.as_ref().and_then(|rhs| lhs.checked_sub(rhs))),
        )
    }
}

impl<T> Sub<&Self> for Checked<T>
where
    T: CheckedSub + CtSelect + Default,
{
    type Output = Checked<T>;

    #[inline]
    fn sub(self, rhs: &Self) -> Self::Output {
        Checked(
            self.0
                .as_ref()
                .and_then(|lhs| rhs.0.as_ref().and_then(|rhs| lhs.checked_sub(rhs))),
        )
    }
}

impl<T> Sub<Checked<T>> for &Checked<T>
where
    T: CheckedSub + CtSelect + Default,
{
    type Output = Checked<T>;

    #[inline]
    fn sub(self, rhs: Checked<T>) -> Self::Output {
        Checked(
            self.0
                .as_ref()
                .and_then(|lhs| rhs.0.as_ref().and_then(|rhs| lhs.checked_sub(rhs))),
        )
    }
}

impl<T> Sub<&Checked<T>> for &Checked<T>
where
    T: CheckedSub + CtSelect + Default,
{
    type Output = Checked<T>;

    #[inline]
    fn sub(self, rhs: &Checked<T>) -> Self::Output {
        Checked(
            self.0
                .as_ref()
                .and_then(|lhs| rhs.0.as_ref().and_then(|rhs| lhs.checked_sub(rhs))),
        )
    }
}

impl<T> Mul<Self> for Checked<T>
where
    T: CheckedMul + CtSelect + Default,
{
    type Output = Checked<T>;

    #[inline]
    fn mul(self, rhs: Self) -> Self::Output {
        Checked(
            self.0
                .as_ref()
                .and_then(|lhs| rhs.0.as_ref().and_then(|rhs| lhs.checked_mul(rhs))),
        )
    }
}

impl<T> Mul<&Self> for Checked<T>
where
    T: CheckedMul + CtSelect + Default,
{
    type Output = Checked<T>;

    #[inline]
    fn mul(self, rhs: &Self) -> Self::Output {
        Checked(
            self.0
                .as_ref()
                .and_then(|lhs| rhs.0.as_ref().and_then(|rhs| lhs.checked_mul(rhs))),
        )
    }
}

impl<T> Mul<Checked<T>> for &Checked<T>
where
    T: CheckedMul + CtSelect + Default,
{
    type Output = Checked<T>;

    #[inline]
    fn mul(self, rhs: Checked<T>) -> Self::Output {
        Checked(
            self.0
                .as_ref()
                .and_then(|lhs| rhs.0.as_ref().and_then(|rhs| lhs.checked_mul(rhs))),
        )
    }
}

impl<T> Mul<&Checked<T>> for &Checked<T>
where
    T: CheckedMul + CtSelect + Default,
{
    type Output = Checked<T>;

    #[inline]
    fn mul(self, rhs: &Checked<T>) -> Self::Output {
        Checked(
            self.0
                .as_ref()
                .and_then(|lhs| rhs.0.as_ref().and_then(|rhs| lhs.checked_mul(rhs))),
        )
    }
}

impl<T> Div<Self> for Checked<T>
where
    T: CheckedDiv + CtSelect + Default,
{
    type Output = Checked<T>;

    #[inline]
    fn div(self, rhs: Self) -> Self::Output {
        Checked(
            self.0
                .as_ref()
                .and_then(|lhs| rhs.0.as_ref().and_then(|rhs| lhs.checked_div(rhs))),
        )
    }
}

impl<T> Div<&Self> for Checked<T>
where
    T: CheckedDiv + CtSelect + Default,
{
    type Output = Checked<T>;

    #[inline]
    fn div(self, rhs: &Self) -> Self::Output {
        Checked(
            self.0
                .as_ref()
                .and_then(|lhs| rhs.0.as_ref().and_then(|rhs| lhs.checked_div(rhs))),
        )
    }
}

impl<T> Div<Checked<T>> for &Checked<T>
where
    T: CheckedDiv + CtSelect + Default,
{
    type Output = Checked<T>;

    #[inline]
    fn div(self, rhs: Checked<T>) -> Self::Output {
        Checked(
            self.0
                .as_ref()
                .and_then(|lhs| rhs.0.as_ref().and_then(|rhs| lhs.checked_div(rhs))),
        )
    }
}

impl<T> Div<&Checked<T>> for &Checked<T>
where
    T: CheckedDiv + CtSelect + Default,
{
    type Output = Checked<T>;

    #[inline]
    fn div(self, rhs: &Checked<T>) -> Self::Output {
        Checked(
            self.0
                .as_ref()
                .and_then(|lhs| rhs.0.as_ref().and_then(|rhs| lhs.checked_div(rhs))),
        )
    }
}

impl<T> CtEq for Checked<T>
where
    T: CtEq,
{
    #[inline]
    fn ct_eq(&self, other: &Self) -> Choice {
        self.0.ct_eq(&other.0)
    }
}

impl<T> CtSelect for Checked<T>
where
    T: CtSelect,
{
    #[inline]
    fn ct_select(&self, other: &Self, choice: Choice) -> Self {
        Self(self.0.ct_select(&other.0, choice))
    }
}

impl<T> Default for Checked<T>
where
    T: Default,
{
    fn default() -> Self {
        Self::new(T::default())
    }
}

impl<T> From<Checked<T>> for CtOption<T> {
    fn from(checked: Checked<T>) -> CtOption<T> {
        checked.0
    }
}

impl<T> From<CtOption<T>> for Checked<T> {
    fn from(ct_option: CtOption<T>) -> Checked<T> {
        Checked(ct_option)
    }
}

impl<T> From<Checked<T>> for Option<T> {
    fn from(checked: Checked<T>) -> Option<T> {
        checked.0.into()
    }
}

#[cfg(feature = "serde")]
impl<'de, T: Default + Deserialize<'de>> Deserialize<'de> for Checked<T> {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let value = Option::<T>::deserialize(deserializer)?;
        let choice = Choice::from_u8_lsb(value.is_some().into());
        Ok(Self(CtOption::new(value.unwrap_or_default(), choice)))
    }
}

#[cfg(feature = "serde")]
impl<T: Copy + Serialize> Serialize for Checked<T> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        self.0.into_option().serialize(serializer)
    }
}

#[cfg(feature = "subtle")]
impl<T> subtle::ConditionallySelectable for Checked<T>
where
    T: Copy,
    Self: CtSelect,
{
    #[inline]
    fn conditional_select(a: &Self, b: &Self, choice: subtle::Choice) -> Self {
        a.ct_select(b, choice.into())
    }
}

#[cfg(feature = "subtle")]
impl<T> subtle::ConstantTimeEq for Checked<T>
where
    Self: CtEq,
{
    #[inline]
    fn ct_eq(&self, rhs: &Self) -> subtle::Choice {
        CtEq::ct_eq(self, rhs).into()
    }
}
