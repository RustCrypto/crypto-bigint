//! Macro definitions which are a part of the public API.

/// Calculate the number of limbs required to represent the given number of bits.
// TODO(tarcieri): replace with `generic_const_exprs` (rust-lang/rust#76560) when stable
#[macro_export]
macro_rules! nlimbs {
    ($bits:expr) => {
        (($bits + $crate::Limb::BITS - 1) / $crate::Limb::BITS) as usize
    };
}

/// Calculate the number of 62-bit unsaturated limbs required to represent the given number of bits when performing
/// Bernstein-Yang inversions.
///
/// We need to ensure that:
///
/// ```text
/// $bits <= (safegcd_nlimbs($bits) * 62) - 64
/// ```
// TODO(tarcieri): replace with `generic_const_exprs` (rust-lang/rust#76560) when stable
macro_rules! safegcd_nlimbs {
    ($bits:expr) => {
        ($bits + 64).div_ceil(62)
    };
}

/// Internal implementation detail of [`const_assert_eq`] and [`const_assert_ne`].
#[doc(hidden)]
#[macro_export]
macro_rules! const_assert_n {
    ($n:ident, $($arg:tt)*) => {{
        // TODO(tarcieri): gensym a name so it's unique per invocation of the macro?
        mod __const_assert {
            pub(super) struct Assert<const $n: usize>;

            impl<const $n: usize> Assert<$n> {
                pub(super) const ASSERT: () = assert!($($arg)*);
            }
        }

        __const_assert::Assert::<$n>::ASSERT
    }};
}

/// Const-friendly assertion that two values are equal.
///
/// The first/leftmost operand MUST be a `usize` constant.
///
/// ```ignore
/// const N: usize = 0;
/// const _: () = crypto_bigint::const_assert_eq!(N, 0, "zero equals zero");
/// ```
#[allow(unused_macros)] // TODO(tarcieri): not ready for external use
macro_rules! const_assert_eq {
    ($left:ident, $right:expr $(,)?) => (
        $crate::const_assert_n!($left, $left == $right)
    );
    ($left:ident, $right:expr, $($arg:tt)+) => (
        $crate::const_assert_n!($left, $left == $right, $($arg)+)
    );
}

/// Const-friendly assertion that two values are NOT equal.
///
/// The first/leftmost operand MUST be a `usize` constant.
///
/// ```ignore
/// const N: usize = 0;
/// const _: () = crypto_bigint::const_assert_ne!(N, 1, "zero is NOT equal to one");
/// ```
macro_rules! const_assert_ne {
    ($left:ident, $right:expr $(,)?) => (
        $crate::const_assert_n!($left, $left != $right)
    );
    ($left:ident, $right:expr, $($arg:tt)+) => (
        $crate::const_assert_n!($left, $left != $right, $($arg)+)
    );
}

#[cfg(test)]
mod tests {
    #[cfg(target_pointer_width = "32")]
    #[test]
    fn nlimbs_for_bits_macro() {
        assert_eq!(nlimbs!(64), 2);
        assert_eq!(nlimbs!(128), 4);
        assert_eq!(nlimbs!(192), 6);
        assert_eq!(nlimbs!(256), 8);
    }

    #[cfg(target_pointer_width = "64")]
    #[test]
    fn nlimbs_for_bits_macro() {
        assert_eq!(nlimbs!(64), 1);
        assert_eq!(nlimbs!(128), 2);
        assert_eq!(nlimbs!(192), 3);
        assert_eq!(nlimbs!(256), 4);
    }
}
