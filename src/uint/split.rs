use crate::{Limb, MatchSize, SplitSize, Uint};

impl<const I: usize> Uint<I> {
    /// Split this number in half into low and high components.
    #[must_use]
    pub const fn split<const O: usize>(&self) -> (Uint<O>, Uint<O>)
    where
        SplitSize<I, O>: MatchSize<Target = Uint<O>>,
    {
        self.split_mixed()
    }

    /// Split this number into low and high components respectively.
    #[inline]
    #[must_use]
    pub const fn split_mixed<const L: usize, const H: usize>(&self) -> (Uint<L>, Uint<H>)
    where
        SplitSize<I, L>: MatchSize<Target = Uint<H>>,
    {
        let top = L + H;
        let top = if top < I { top } else { I };
        let mut lo = [Limb::ZERO; L];
        let mut hi = [Limb::ZERO; H];
        let mut i = 0;

        while i < top {
            if i < L {
                lo[i] = self.limbs[i];
            } else {
                hi[i - L] = self.limbs[i];
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
