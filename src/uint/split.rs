use crate::{Split, Uint};

const fn split<const I: usize, const L: usize, const H: usize>(
    value: &Uint<I>,
) -> (Uint<L>, Uint<H>) {
    const {
        assert!(
            L + H == I,
            concat![
                "The sum of the sizes of the declared types of `Uint` split is not equal to ",
                "the size of the input type. ",
            ]
        );
    }

    let mut lo = Uint::<L>::ZERO;
    let mut hi = Uint::<H>::ZERO;

    let mut i = 0;
    while i < L {
        lo.limbs[i] = value.limbs[i];
        i += 1;
    }
    while i < L + H {
        hi.limbs[i - L] = value.limbs[i];
        i += 1;
    }

    (lo, hi)
}

impl<const L: usize, const H: usize, const O: usize> Split<Uint<L>, Uint<H>> for Uint<O> {
    /// Split this number into low and high components respectively.
    ///
    /// <div class="warning">
    /// The sum of output lengths must be equal to the input length.
    /// </div>
    fn split(&self) -> (Uint<L>, Uint<H>) {
        self.split_mixed()
    }
}

impl<const I: usize> Uint<I> {
    /// Split this number in half into low and high components.
    ///
    /// <div class="warning">
    /// The sum of output lengths must be equal to the input length.
    /// </div>
    pub const fn split<const O: usize>(&self) -> (Uint<O>, Uint<O>) {
        split::<I, O, O>(self)
    }

    /// Split this number into low and high components respectively.
    ///
    /// <div class="warning">
    /// The sum of output lengths must be equal to the input length.
    /// </div>
    pub const fn split_mixed<const L: usize, const H: usize>(&self) -> (Uint<L>, Uint<H>) {
        split::<I, L, H>(self)
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
