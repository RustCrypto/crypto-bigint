//! Constant-time helper functions.
//!
//! These largely exist as a workaround for the `Copy` bound on [`subtle::ConditionallySelectable`].

use super::BoxedUint;
use subtle::CtOption;

impl BoxedUint {
    /// Conditional `map`: workaround which provides a [`CtOption::map`]-like API.
    ///
    /// Ensures both functions are called regardless of whether the first returns some/none with an
    /// argument whose precision matches `self`. Note this still requires branching on the
    /// intermediate [`CtOption`] value and therefore isn't fully constant time, but the best we can
    /// do without upstream changes to `subtle` (see dalek-cryptography/subtle#94).
    ///
    /// Workaround due to `Copy` in [`subtle::ConditionallySelectable`] supertrait bounds.
    pub fn cond_map<C, F, T>(&self, condition: C, f: F) -> CtOption<T>
    where
        C: Fn(&Self) -> CtOption<Self>,
        F: Fn(Self) -> T,
    {
        let cond_val = condition(self);
        let is_some = cond_val.is_some();

        let placeholder = Self::zero_with_precision(self.bits_precision());
        let value = Option::<Self>::from(cond_val).unwrap_or(placeholder);
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
    /// Workaround due to `Copy` in [`subtle::ConditionallySelectable`] supertrait bounds.
    pub fn cond_and_then<C, F>(&self, condition: C, f: F) -> CtOption<Self>
    where
        C: Fn(&Self) -> CtOption<Self>,
        F: Fn(Self) -> CtOption<Self>,
    {
        let cond_val = condition(self);
        let mut is_some = cond_val.is_some();

        let placeholder = Self::zero_with_precision(self.bits_precision());
        let value = Option::<Self>::from(cond_val).unwrap_or(placeholder);
        debug_assert_eq!(self.bits_precision(), value.bits_precision());

        let cond_val = f(value);
        is_some &= cond_val.is_some();

        let placeholder = Self::zero_with_precision(self.bits_precision());
        let value = Option::from(cond_val).unwrap_or(placeholder);
        debug_assert_eq!(self.bits_precision(), value.bits_precision());

        CtOption::new(value, is_some)
    }
}

#[cfg(test)]
mod tests {
    use super::BoxedUint;
    use subtle::CtOption;

    #[test]
    fn cond_map_some() {
        let n = BoxedUint::one();

        let ret = n
            .cond_map(
                |n| CtOption::new(n.clone(), 1u8.into()),
                |n| n.wrapping_add(&BoxedUint::one()),
            )
            .unwrap();

        assert_eq!(ret, BoxedUint::from(2u8));
    }

    #[test]
    fn cond_map_none() {
        let n = BoxedUint::one();

        let ret = n.cond_map(
            |n| CtOption::new(n.clone(), 0u8.into()),
            |n| n.wrapping_add(&BoxedUint::one()),
        );

        assert!(bool::from(ret.is_none()));
    }

    #[test]
    fn cond_and_then_all_some() {
        let n = BoxedUint::one();

        let ret = n
            .cond_and_then(
                |n| CtOption::new(n.clone(), 1u8.into()),
                |n| CtOption::new(n.wrapping_add(&BoxedUint::one()), 1u8.into()),
            )
            .unwrap();

        assert_eq!(ret, BoxedUint::from(2u8));
    }

    macro_rules! cond_and_then_none_test {
        ($name:ident, $a:expr, $b:expr) => {
            #[test]
            fn $name() {
                let n = BoxedUint::one();

                let ret = n.cond_and_then(
                    |n| CtOption::new(n.clone(), $a.into()),
                    |n| CtOption::new(n.wrapping_add(&BoxedUint::one()), $b.into()),
                );

                assert!(bool::from(ret.is_none()));
            }
        };
    }

    cond_and_then_none_test!(cond_and_then_none_some, 0, 1);
    cond_and_then_none_test!(cond_and_then_some_none, 1, 0);
    cond_and_then_none_test!(cond_and_then_none_none, 0, 0);
}
