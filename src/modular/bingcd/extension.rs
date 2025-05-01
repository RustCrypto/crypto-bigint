use crate::{ConstChoice, Limb, Uint};

pub(crate) struct ExtendedUint<const LIMBS: usize, const EXTENSION_LIMBS: usize>(
    Uint<LIMBS>,
    Uint<EXTENSION_LIMBS>,
);

impl<const LIMBS: usize, const EXTRA: usize> ExtendedUint<LIMBS, EXTRA> {
    /// Construct an [ExtendedUint] from the product of a [Uint<LIMBS>] and an [Uint<EXTRA>].
    ///
    /// Assumes the top bit of the product is not set.
    #[inline]
    pub const fn from_product(lhs: Uint<LIMBS>, rhs: Uint<EXTRA>) -> Self {
        let (lo, hi) = lhs.split_mul(&rhs);
        ExtendedUint(lo, hi)
    }

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
    pub const fn from_product(lhs: Uint<LIMBS>, rhs: Uint<EXTRA>) -> Self {
        ExtendedUint::from_product(lhs, rhs).as_extended_int()
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

    /// Compute `self - rhs`, wrapping any underflow.
    #[inline]
    pub const fn wrapping_sub(&self, rhs: &Self) -> Self {
        let (lo, borrow) = self.0.sbb(&rhs.0, Limb::ZERO);
        let (hi, _) = self.1.sbb(&rhs.1, borrow);
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

#[cfg(test)]
mod tests {
    use crate::modular::bingcd::extension::ExtendedUint;
    use crate::{U64, Uint};

    const A: ExtendedUint<{ U64::LIMBS }, { U64::LIMBS }> = ExtendedUint::from_product(
        U64::from_u64(68146184546341u64),
        U64::from_u64(873817114763u64),
    );
    const B: ExtendedUint<{ U64::LIMBS }, { U64::LIMBS }> = ExtendedUint::from_product(
        U64::from_u64(7772181434148543u64),
        U64::from_u64(6665138352u64),
    );

    impl<const LIMBS: usize, const EXTRA: usize> ExtendedUint<LIMBS, EXTRA> {
        /// Decompose `self` into the bottom and top limbs.
        #[inline]
        const fn as_elements(&self) -> (Uint<LIMBS>, Uint<EXTRA>) {
            (self.0, self.1)
        }
    }

    #[test]
    fn test_from_product() {
        assert_eq!(
            A.as_elements(),
            (U64::from(13454091406951429143u64), U64::from(3228065u64))
        );
        assert_eq!(
            B.as_elements(),
            (U64::from(1338820589698724688u64), U64::from(2808228u64))
        );
    }

    #[test]
    fn test_wrapping_sub() {
        assert_eq!(
            A.as_extended_int()
                .wrapping_sub(&B.as_extended_int())
                .as_extended_uint()
                .as_elements(),
            (U64::from(12115270817252704455u64), U64::from(419837u64))
        )
    }
}
