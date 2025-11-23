use crate::{Concat, Uint};

const fn concat<const L: usize, const H: usize, const O: usize>(
    lo: &Uint<L>,
    hi: &Uint<H>,
) -> Uint<O> {
    const {
        assert!(
            L + H == O,
            concat![
                "The size of the declared type of `Uint` concatenation is not equal to ",
                "the sum of the sizes of argument types. ",
            ]
        );
    }

    let mut result = Uint::<O>::ZERO;

    let mut i = 0;
    while i < L {
        result.limbs[i] = lo.limbs[i];
        i += 1;
    }
    while i < L + H {
        result.limbs[i] = hi.limbs[i - L];
        i += 1;
    }

    result
}

impl<const L: usize, const H: usize, const O: usize> Concat<Uint<O>, Uint<H>> for Uint<L> {
    /// Concatenate the two values, with `self` as least significant and `hi` as the most
    /// significant.
    ///
    /// <div class="warning">
    /// The sum of input lengths must be equal to the output length.
    /// </div>
    fn concat(&self, hi: &Uint<H>) -> Uint<O> {
        self.concat_mixed(hi)
    }
}

impl<const L: usize> Uint<L> {
    /// Concatenate the two values, with `self` as least significant and `hi` as the most
    /// significant.
    ///
    /// <div class="warning">
    /// The sum of input lengths must be equal to the output length.
    /// </div>
    pub const fn concat<const O: usize>(&self, hi: &Self) -> Uint<O> {
        concat(self, hi)
    }

    /// Concatenate the two values, with `self` as least significant and `hi`
    /// as the most significant.
    ///
    /// <div class="warning">
    /// The sum of input lengths must be equal to the output length.
    /// </div>
    #[inline]
    pub const fn concat_mixed<const H: usize, const O: usize>(&self, hi: &Uint<H>) -> Uint<O> {
        concat(self, hi)
    }
}

#[cfg(test)]
mod tests {
    use crate::{U64, U128, U192};

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
}
