use crate::{Concat, Uint};

impl<const LIMBS: usize> Uint<LIMBS> {
    /// Concatenate the two values, with `self` as least significant and `hi` as the most
    /// significant, with both values having the same size.
    #[must_use]
    pub const fn concat<const WIDE_LIMBS: usize>(&self, hi: &Self) -> Uint<WIDE_LIMBS>
    where
        Self: Concat<LIMBS, Output = Uint<WIDE_LIMBS>>,
    {
        Uint::concat_mixed(self, hi)
    }

    /// Concatenate the two values, with `self` as least significant and `hi`
    /// as the most significant.
    #[inline]
    #[must_use]
    pub const fn concat_mixed<const HI_LIMBS: usize, const WIDE_LIMBS: usize>(
        &self,
        hi: &Uint<HI_LIMBS>,
    ) -> Uint<WIDE_LIMBS>
    where
        Self: Concat<HI_LIMBS, Output = Uint<WIDE_LIMBS>>,
    {
        let mut res = Uint::ZERO;
        let (res_lo, res_hi) = res.as_mut_uint_ref().split_at_mut(LIMBS);
        res_lo.copy_from(self.as_uint_ref());
        res_hi.copy_from(hi.as_uint_ref());
        res
    }
}

#[cfg(test)]
mod tests {
    use crate::{BitOps, U64, U128, U192, Uint};

    #[test]
    fn concat() {
        let hi = U64::from_u64(0x0011223344556677);
        let lo = U64::from_u64(0x8899aabbccddeeff);
        assert_eq!(
            lo.concat(&hi),
            U128::from_be_hex("00112233445566778899aabbccddeeff")
        );
    }

    #[test]
    fn concat_mixed() {
        let hi = U64::from_u64(0x0011223344556677);
        let lo = U128::from_u128(0x8899aabbccddeeff_8899aabbccddeeff);
        assert_eq!(
            lo.concat_mixed(&hi),
            U192::from_be_hex("00112233445566778899aabbccddeeff8899aabbccddeeff")
        );
        assert_eq!(
            hi.concat_mixed(&lo),
            U192::from_be_hex("8899aabbccddeeff8899aabbccddeeff0011223344556677")
        );
    }

    #[test]
    fn convert() {
        let res: U128 = U64::ONE.widening_mul(&U64::ONE).into();
        assert_eq!(res, U128::ONE);

        let res: U128 = U64::ONE.square_wide().into();
        assert_eq!(res, U128::ONE);
    }

    #[test]
    fn infer_sizes() {
        let wide = U64::ONE.concat(&Uint::ZERO);
        assert_eq!(wide.bits_precision(), 128);
        assert_eq!(wide, Uint::ONE);

        let wide = U64::ONE.concat_mixed(&U128::ZERO);
        assert_eq!(wide.bits_precision(), 192);
        assert_eq!(wide, Uint::ONE);
    }
}
