use crate::{Limb, Split, SplitMixed, Uint};

const fn split_mixed<const I: usize, const L: usize, const H: usize>(
    value: &Uint<I>,
) -> (Uint<L>, Uint<H>) {
    const {
        if L + H != I {
            panic!(
                "The sum of widths of low and high parts after the split must be equal to the width of the input"
            );
        }
    }

    let mut lo = Uint::<L>::ZERO;
    let mut hi = Uint::<H>::ZERO;

    let mut i = 0;
    while i < L {
        lo.limbs[i] = value.limbs[i];
        i += 1;
    }
    while i < H {
        hi.limbs[i - L] = value.limbs[i];
        i += 1;
    }

    (lo, hi)
}

impl<const I: usize> Uint<I> {
    /// Split this number in half into low and high components.
    pub const fn split<const O: usize>(&self) -> (Uint<O>, Uint<O>)
    where
        Self: Split<Output = Uint<O>>,
    {
        self.split_mixed()
    }

    /// Split this number into low and high components respectively.
    #[inline]
    pub const fn split_mixed<const L: usize, const H: usize>(&self) -> (Uint<L>, Uint<H>)
    where
        Self: SplitMixed<Uint<L>, Uint<H>>,
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

    /// Split this number in half into low and high components.
    pub const fn new_split<const O: usize>(&self) -> (Uint<O>, Uint<O>) {
        split_mixed(self)
    }

    /// Split this number into low and high components respectively.
    pub const fn new_split_mixed<const L: usize, const H: usize>(&self) -> (Uint<L>, Uint<H>) {
        split_mixed(self)
    }
}

#[cfg(test)]
mod tests {
    use crate::{U64, U128};

    #[test]
    fn split() {
        let (lo, hi) = U128::from_be_hex("00112233445566778899aabbccddeeff").split();
        assert_eq!(lo, U64::from_u64(0x8899aabbccddeeff));
        assert_eq!(hi, U64::from_u64(0x0011223344556677));
    }
}
