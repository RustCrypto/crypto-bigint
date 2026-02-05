use crate::{ConcatSize, Limb, MatchSize, Uint};

impl<const L: usize> Uint<L> {
    /// Concatenate the two values, with `self` as least significant and `hi` as the most
    /// significant.
    #[must_use]
    pub const fn concat<const O: usize>(&self, hi: &Self) -> Uint<O>
    where
        ConcatSize<L, L>: MatchSize<Target = Uint<O>>,
    {
        Uint::concat_mixed(self, hi)
    }

    /// Concatenate the two values, with `lo` as least significant and `hi`
    /// as the most significant.
    #[inline]
    #[must_use]
    pub const fn concat_mixed<const H: usize, const O: usize>(&self, hi: &Uint<H>) -> Uint<O>
    where
        ConcatSize<L, H>: MatchSize<Target = Uint<O>>,
    {
        let top = L + H;
        let top = if top < O { top } else { O };
        let mut limbs = [Limb::ZERO; O];
        let mut i = 0;

        while i < top {
            if i < L {
                limbs[i] = self.limbs[i];
            } else {
                limbs[i] = hi.limbs[i - L];
            }
            i += 1;
        }

        Uint { limbs }
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
