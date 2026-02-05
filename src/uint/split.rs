use crate::{Limb, MatchSize, SplitSize, Uint};

impl<const LIMBS: usize> Uint<LIMBS> {
    /// Split the limbs of this `Uint` into low and high components of the same size.
    #[must_use]
    pub const fn split<const HALF_LIMBS: usize>(&self) -> (Uint<HALF_LIMBS>, Uint<HALF_LIMBS>)
    where
        SplitSize<LIMBS, HALF_LIMBS>: MatchSize<Target = Uint<HALF_LIMBS>>,
    {
        self.split_mixed()
    }

    /// Split the limbs of this `Uint` into low and high components.
    #[inline]
    #[must_use]
    pub const fn split_mixed<const LO_LIMBS: usize, const HI_LIMBS: usize>(
        &self,
    ) -> (Uint<LO_LIMBS>, Uint<HI_LIMBS>)
    where
        SplitSize<LIMBS, LO_LIMBS>: MatchSize<Target = Uint<HI_LIMBS>>,
    {
        let top = LO_LIMBS + HI_LIMBS;
        let top = if top < LIMBS { top } else { LIMBS };
        let mut lo = [Limb::ZERO; LO_LIMBS];
        let mut hi = [Limb::ZERO; HI_LIMBS];
        let mut i = 0;

        while i < top {
            if i < LO_LIMBS {
                lo[i] = self.limbs[i];
            } else {
                hi[i - LO_LIMBS] = self.limbs[i];
            }
            i += 1;
        }

        (Uint { limbs: lo }, Uint { limbs: hi })
    }
}

#[cfg(test)]
mod tests {
    use crate::{BitOps, U64, U128, U192, Uint};

    #[test]
    fn split() {
        let (lo, hi) = U128::from_be_hex("00112233445566778899aabbccddeeff").split();
        assert_eq!(lo, U64::from_u64(0x8899aabbccddeeff));
        assert_eq!(hi, U64::from_u64(0x0011223344556677));
    }

    #[test]
    fn infer_sizes() {
        let (lo, hi) = U128::ONE.split();
        assert_eq!(lo.bits_precision(), 64);
        assert_eq!(lo, Uint::ONE);
        assert_eq!(hi.bits_precision(), 64);
        assert_eq!(hi, Uint::ZERO);

        let (lo, hi) = U192::ONE.split_mixed();
        assert_eq!(lo, U64::ONE);
        assert_eq!(hi.bits_precision(), 128);
        assert_eq!(hi, Uint::ZERO);
    }
}
