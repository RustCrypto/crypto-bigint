use crate::{ConstChoice, Uint};

/// `const` equivalent of `u32::max(a, b)`.
pub(crate) const fn const_max(a: u32, b: u32) -> u32 {
    ConstChoice::from_u32_lt(a, b).select_u32(a, b)
}

/// `const` equivalent of `u32::min(a, b)`.
pub(crate) const fn const_min(a: u32, b: u32) -> u32 {
    ConstChoice::from_u32_lt(a, b).select_u32(b, a)
}

impl<const LIMBS: usize> Uint<LIMBS> {
    /// Construct a [Uint] containing the bits in `self` in the range `[idx, idx + length)`.
    ///
    /// Assumes `length ≤ Uint::<SECTION_LIMBS>::BITS` and `idx + length ≤ Self::BITS`.
    #[inline(always)]
    pub(super) const fn section<const SECTION_LIMBS: usize>(
        &self,
        idx: u32,
        length: u32,
    ) -> Uint<SECTION_LIMBS> {
        debug_assert!(length <= Uint::<SECTION_LIMBS>::BITS);
        debug_assert!(idx + length <= Self::BITS);

        let mask = Uint::ONE.shl(length).wrapping_sub(&Uint::ONE);
        self.shr(idx).resize::<SECTION_LIMBS>().bitand(&mask)
    }

    /// Construct a [Uint] containing the bits in `self` in the range `[idx, idx + length)`.
    ///
    /// Assumes `length ≤ Uint::<SECTION_LIMBS>::BITS` and `idx + length ≤ Self::BITS`.
    ///
    /// Executes in time variable in `idx` only.
    #[inline(always)]
    pub(super) const fn section_vartime<const SECTION_LIMBS: usize>(
        &self,
        idx: u32,
        length: u32,
    ) -> Uint<SECTION_LIMBS> {
        debug_assert!(length <= Uint::<SECTION_LIMBS>::BITS);
        debug_assert!(idx + length <= Self::BITS);

        let mask = Uint::ONE.shl_vartime(length).wrapping_sub(&Uint::ONE);
        self.shr_vartime(idx)
            .resize::<SECTION_LIMBS>()
            .bitand(&mask)
    }

    /// Compact `self` to a form containing the concatenation of its bit ranges `[0, k-1)`
    /// and `[n-k-1, n)`.
    ///
    /// Assumes `k ≤ Uint::<SUMMARY_LIMBS>::BITS`, `n ≤ Self::BITS` and `n ≥ 2k`.
    #[inline(always)]
    pub(super) const fn compact<const SUMMARY_LIMBS: usize>(
        &self,
        n: u32,
        k: u32,
    ) -> Uint<SUMMARY_LIMBS> {
        debug_assert!(k <= Uint::<SUMMARY_LIMBS>::BITS);
        debug_assert!(n <= Self::BITS);
        debug_assert!(n >= 2 * k);

        let hi = self.section(n - k - 1, k + 1);
        let lo = self.section_vartime(0, k - 1);
        hi.shl_vartime(k - 1).bitxor(&lo)
    }
}
