use crate::{ConstChoice, Int, Limb, Uint};

pub(crate) struct ExtendedUint<const LIMBS: usize, const EXTENSION_LIMBS: usize>(
    Uint<LIMBS>,
    Uint<EXTENSION_LIMBS>,
);

impl<const LIMBS: usize, const EXTRA: usize> ExtendedUint<LIMBS, EXTRA> {
    /// Interpret `self` as an [ExtendedInt]
    #[inline]
    pub const fn as_extended_int(&self) -> ExtendedInt<LIMBS, EXTRA> {
        ExtendedInt(self.0, self.1)
    }

    /// Construction the binary negation of `self`, i.e., map `self` to `!self + 1`.
    ///
    /// Note: maps `0` to itself.
    #[inline]
    pub const fn wrapping_neg(&self) -> Self {
        let (lhs, carry) = self.0.carrying_neg();
        let mut rhs = self.1.not();
        rhs = Uint::select(&rhs, &rhs.wrapping_add(&Uint::ONE), carry);
        Self(lhs, rhs)
    }

    /// Negate `self` if `negate` is truthy. Otherwise returns `self`.
    #[inline]
    pub const fn wrapping_neg_if(&self, negate: ConstChoice) -> Self {
        let neg = self.wrapping_neg();
        Self(
            Uint::select(&self.0, &neg.0, negate),
            Uint::select(&self.1, &neg.1, negate),
        )
    }

    /// Shift `self` right by `shift` bits.
    ///
    /// Assumes `shift <= Uint::<EXTRA>::BITS`.
    #[inline]
    pub const fn shr(&self, shift: u32) -> Self {
        debug_assert!(shift <= Uint::<EXTRA>::BITS);

        let shift_is_zero = ConstChoice::from_u32_eq(shift, 0);
        let left_shift = shift_is_zero.select_u32(Uint::<EXTRA>::BITS - shift, 0);

        let hi = self.1.shr(shift);
        // TODO: replace with carrying_shl
        let carry = Uint::select(&self.1, &Uint::ZERO, shift_is_zero).shl(left_shift);
        let mut lo = self.0.shr(shift);

        // Apply carry
        let limb_diff = LIMBS.wrapping_sub(EXTRA) as u32;
        // safe to vartime; shr_vartime is variable in the value of shift only. Since this shift
        // is a public constant, the constant time property of this algorithm is not impacted.
        let carry = carry.resize::<LIMBS>().shl_vartime(limb_diff * Limb::BITS);
        lo = lo.bitxor(&carry);

        Self(lo, hi)
    }
}

#[derive(Debug, PartialEq)]
pub(crate) struct ExtendedInt<const LIMBS: usize, const EXTENSION_LIMBS: usize>(
    Uint<LIMBS>,
    Uint<EXTENSION_LIMBS>,
);

impl<const LIMBS: usize, const EXTRA: usize> ExtendedInt<LIMBS, EXTRA> {
    /// Construct an [ExtendedInt] from the product of a [Uint<LIMBS>] and an [Int<EXTRA>].
    ///
    /// Assumes the top bit of the product is not set.
    #[inline]
    pub const fn from_product(lhs: Uint<LIMBS>, rhs: Int<EXTRA>) -> Self {
        let (lo, hi, sgn) = rhs.split_mul_uint_right(&lhs);
        ExtendedUint(lo, hi).wrapping_neg_if(sgn).as_extended_int()
    }

    /// Interpret this as an [ExtendedUint].
    #[inline]
    pub const fn as_extended_uint(&self) -> ExtendedUint<LIMBS, EXTRA> {
        ExtendedUint(self.0, self.1)
    }

    /// Return the negation of `self` if `negate` is truthy. Otherwise, return `self`.
    #[inline]
    pub const fn wrapping_neg_if(&self, negate: ConstChoice) -> Self {
        self.as_extended_uint()
            .wrapping_neg_if(negate)
            .as_extended_int()
    }

    /// Compute `self + rhs`, wrapping any overflow.
    #[inline]
    pub const fn wrapping_add(&self, rhs: &Self) -> Self {
        let (lo, carry) = self.0.adc(&rhs.0, Limb::ZERO);
        let (hi, _) = self.1.adc(&rhs.1, carry);
        Self(lo, hi)
    }

    /// Returns self without the extension.
    #[inline]
    pub const fn wrapping_drop_extension(&self) -> (Uint<LIMBS>, ConstChoice) {
        let (abs, sgn) = self.abs_sgn();
        (abs.0, sgn)
    }

    /// Decompose `self` into is absolute value and signum.
    #[inline]
    pub const fn abs_sgn(&self) -> (ExtendedUint<LIMBS, EXTRA>, ConstChoice) {
        let is_negative = self.1.as_int().is_negative();
        (
            self.wrapping_neg_if(is_negative).as_extended_uint(),
            is_negative,
        )
    }

    /// Divide self by `2^k`, rounding towards zero.
    #[inline]
    pub const fn div_2k(&self, k: u32) -> Self {
        let (abs, sgn) = self.abs_sgn();
        abs.shr(k).wrapping_neg_if(sgn).as_extended_int()
    }
}
