//! Constant-time helper functions.

use super::BoxedUint;
use crate::Limb;
use subtle::{Choice, ConditionallySelectable, CtOption};

impl BoxedUint {
    /// Conditionally select `a` or `b` in constant time depending on [`Choice`].
    ///
    /// NOTE: can't impl `subtle`'s [`ConditionallySelectable`] trait due to its `Copy` bound, so
    /// this is an inherent function instead.
    ///
    /// Panics if `a` and `b` don't have the same precision.
    pub fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
        debug_assert_eq!(a.bits_precision(), b.bits_precision());
        let mut limbs = vec![Limb::ZERO; a.nlimbs()].into_boxed_slice();

        for i in 0..a.nlimbs() {
            limbs[i] = Limb::conditional_select(&a.limbs[i], &b.limbs[i], choice);
        }

        Self { limbs }
    }

    /// Conditionally assign `other` to `self`, according to `choice`.
    ///
    /// NOTE: can't impl `subtle`'s [`ConditionallySelectable`] trait due to its `Copy` bound, so
    /// this is an inherent function instead.
    ///
    /// Panics if `a` and `b` don't have the same precision.
    #[inline]
    pub fn conditional_assign(&mut self, other: &Self, choice: Choice) {
        debug_assert_eq!(self.bits_precision(), other.bits_precision());

        for i in 0..self.nlimbs() {
            self.limbs[i].conditional_assign(&other.limbs[i], choice);
        }
    }

    /// Conditionally swap `self` and `other` if `choice == 1`; otherwise,
    /// reassign both unto themselves.
    ///
    /// NOTE: can't impl `subtle`'s [`ConditionallySelectable`] trait due to its `Copy` bound, so
    /// this is an inherent function instead.
    ///
    /// Panics if `a` and `b` don't have the same precision.
    #[inline]
    pub fn conditional_swap(a: &mut Self, b: &mut Self, choice: Choice) {
        debug_assert_eq!(a.bits_precision(), b.bits_precision());

        for i in 0..a.nlimbs() {
            Limb::conditional_swap(&mut a.limbs[i], &mut b.limbs[i], choice);
        }
    }

    /// Conditional `map`: workaround which provides a [`CtOption::map`]-like API.
    ///
    /// Ensures both functions are called regardless of whether the first returns some/none with an
    /// argument whose precision matches `self`. Note this still requires branching on the
    /// intermediate [`CtOption`] value and therefore isn't fully constant time, but the best we can
    /// do without upstream changes to `subtle` (see dalek-cryptography/subtle#94).
    ///
    /// Workaround due to `Copy` in [`ConditionallySelectable`] supertrait bounds.
    pub fn conditional_map<C, F, T>(&self, condition: C, f: F) -> CtOption<T>
    where
        C: Fn(&Self) -> CtOption<Self>,
        F: Fn(Self) -> T,
    {
        let conditional_val = condition(self);
        let is_some = conditional_val.is_some();

        let placeholder = Self::zero_with_precision(self.bits_precision());
        let value = Option::<Self>::from(conditional_val).unwrap_or(placeholder);
        debug_assert_eq!(self.bits_precision(), value.bits_precision());
        CtOption::new(f(value), is_some)
    }

    /// Conditional `and_then`: workaround which provides a [`CtOption::and_then`]-like API.
    ///
    /// Ensures both functions are called regardless of whether the first returns some/none with an
    /// argument whose precision matches `self`. Note this still requires branching on the
    /// intermediate [`CtOption`] value and therefore isn't fully constant time, but the best we can
    /// do without upstream changes to `subtle` (see dalek-cryptography/subtle#94).
    ///
    /// Workaround due to `Copy` in [`ConditionallySelectable`] supertrait bounds.
    pub fn conditional_and_then<C, F>(&self, condition: C, f: F) -> CtOption<Self>
    where
        C: Fn(&Self) -> CtOption<Self>,
        F: Fn(Self) -> CtOption<Self>,
    {
        let conditional_val = condition(self);
        let mut is_some = conditional_val.is_some();

        let placeholder = Self::zero_with_precision(self.bits_precision());
        let value = Option::<Self>::from(conditional_val).unwrap_or(placeholder);
        debug_assert_eq!(self.bits_precision(), value.bits_precision());

        let conditional_val = f(value);
        is_some &= conditional_val.is_some();

        let placeholder = Self::zero_with_precision(self.bits_precision());
        let value = Option::from(conditional_val).unwrap_or(placeholder);
        debug_assert_eq!(self.bits_precision(), value.bits_precision());

        CtOption::new(value, is_some)
    }
}

#[cfg(test)]
mod tests {
    use super::BoxedUint;
    use subtle::{Choice, CtOption};

    #[test]
    fn conditional_select() {
        let a = BoxedUint::zero_with_precision(128);
        let b = BoxedUint::max(128);

        assert_eq!(a, BoxedUint::conditional_select(&a, &b, Choice::from(0)));
        assert_eq!(b, BoxedUint::conditional_select(&a, &b, Choice::from(1)));
    }

    #[test]
    fn conditional_map_some() {
        let n = BoxedUint::one();

        let ret = n
            .conditional_map(
                |n| CtOption::new(n.clone(), 1u8.into()),
                |n| n.wrapping_add(&BoxedUint::one()),
            )
            .unwrap();

        assert_eq!(ret, BoxedUint::from(2u8));
    }

    #[test]
    fn conditional_map_none() {
        let n = BoxedUint::one();

        let ret = n.conditional_map(
            |n| CtOption::new(n.clone(), 0u8.into()),
            |n| n.wrapping_add(&BoxedUint::one()),
        );

        assert!(bool::from(ret.is_none()));
    }

    #[test]
    fn conditional_and_then_all_some() {
        let n = BoxedUint::one();

        let ret = n
            .conditional_and_then(
                |n| CtOption::new(n.clone(), 1u8.into()),
                |n| CtOption::new(n.wrapping_add(&BoxedUint::one()), 1u8.into()),
            )
            .unwrap();

        assert_eq!(ret, BoxedUint::from(2u8));
    }

    macro_rules! conditional_and_then_none_test {
        ($name:ident, $a:expr, $b:expr) => {
            #[test]
            fn $name() {
                let n = BoxedUint::one();

                let ret = n.conditional_and_then(
                    |n| CtOption::new(n.clone(), $a.into()),
                    |n| CtOption::new(n.wrapping_add(&BoxedUint::one()), $b.into()),
                );

                assert!(bool::from(ret.is_none()));
            }
        };
    }

    conditional_and_then_none_test!(conditional_and_then_none_some, 0, 1);
    conditional_and_then_none_test!(conditional_and_then_some_none, 1, 0);
    conditional_and_then_none_test!(conditional_and_then_none_none, 0, 0);
}
