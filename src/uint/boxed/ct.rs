//! Constant-time helpers.
//!
//! These are primarily workarounds for things we can't fix in `subtle` without upstream changes,
//! namely the `Copy` bound on `ConditionallySelectable`.

use super::BoxedUint;
use subtle::CtOption;

impl BoxedUint {
    /// Equivalent to [`CtOption::map`], but works around the `Copy` bound on
    /// `ConditionallySelectable`.
    ///
    /// Accepts the bits of precision that the value is expected to have if it's some.
    ///
    /// NOTE: not fully constant-time, but the best we can do given the circumstances.
    /// Ensures the closure is always called.
    pub(crate) fn ct_map<F>(bits_precision: usize, ct_opt: CtOption<Self>, f: F) -> CtOption<Self>
    where
        F: FnOnce(Self) -> Self,
    {
        let is_some = ct_opt.is_some();
        let zero = Self::zero_with_precision(bits_precision);

        // NOTE: variable-time, but anything else would require upstream changes to `subtle`
        let value = Option::<Self>::from(ct_opt).unwrap_or(zero);

        CtOption::new(f(value), is_some)
    }

    /// Equivalent to [`CtOption::map`], but works around the `Copy` bound on
    /// `ConditionallySelectable`.
    ///
    /// Accepts the bits of precision that the value is expected to have if it's some.
    ///
    /// NOTE: not fully constant-time, but the best we can do given the circumstances.
    /// Ensures the closure is always called.
    #[inline]
    pub(crate) fn ct_and_then<F>(
        bits_precision: usize,
        ct_opt: CtOption<Self>,
        f: F,
    ) -> CtOption<Self>
    where
        F: FnOnce(Self) -> CtOption<Self>,
    {
        let mut is_some = ct_opt.is_some();
        let zero = Self::zero_with_precision(bits_precision);

        // NOTE: variable-time, but anything else would require upstream changes to `subtle`
        let value = Option::from(ct_opt).unwrap_or_else(|| zero.clone());
        let ret = f(value);
        is_some &= ret.is_some();

        CtOption::new(Option::from(ret).unwrap_or(zero), is_some)
    }
}
