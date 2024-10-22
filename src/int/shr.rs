//! [`Int`] bitwise right shift operations.

use core::ops::{Shr, ShrAssign};

use subtle::CtOption;

use crate::{ConstChoice, ConstCtOption, Int, ShrVartime, Uint, WrappingShr};

impl<const LIMBS: usize> Int<LIMBS> {
    /// Computes `self >> shift`.
    ///
    /// Note, this is signed shift right, i.e., the value shifted in on the left is equal to
    /// the most significant bit.
    ///
    /// Panics if `shift >= Self::BITS`.
    pub const fn shr(&self, shift: u32) -> Self {
        self.overflowing_shr(shift)
            .expect("`shift` within the bit size of the integer")
    }

    /// Computes `self >> shift` in variable time.
    ///
    /// Note, this is signed shift right, i.e., the value shifted in on the left is equal to
    /// the most significant bit.
    ///
    /// Panics if `shift >= Self::BITS`.
    pub const fn shr_vartime(&self, shift: u32) -> Self {
        self.overflowing_shr_vartime(shift)
            .expect("`shift` within the bit size of the integer")
    }

    /// Computes `self >> shift`.
    ///
    /// Note, this is signed shift right, i.e., the value shifted in on the left is equal to
    /// the most significant bit.
    ///
    /// Returns `None` if `shift >= Self::BITS`.
    pub const fn overflowing_shr(&self, shift: u32) -> ConstCtOption<Self> {
        // `floor(log2(BITS - 1))` is the number of bits in the representation of `shift`
        // (which lies in range `0 <= shift < BITS`).
        let shift_bits = u32::BITS - (Self::BITS - 1).leading_zeros();
        let overflow = ConstChoice::from_u32_lt(shift, Self::BITS).not();
        let shift = shift % Self::BITS;
        let mut result = *self;
        let mut i = 0;
        while i < shift_bits {
            let bit = ConstChoice::from_u32_lsb((shift >> i) & 1);
            result = Int::select(
                &result,
                &result
                    .overflowing_shr_vartime(1 << i)
                    .expect("shift within range"),
                bit,
            );
            i += 1;
        }

        ConstCtOption::new(result, overflow.not())
    }

    /// Computes `self >> shift`.
    ///
    /// Returns `None` if `shift >= Self::BITS`.
    ///
    /// NOTE: this operation is variable time with respect to `shift` *ONLY*.
    ///
    /// When used with a fixed `shift`, this function is constant-time with respect
    /// to `self`.
    #[inline(always)]
    pub const fn overflowing_shr_vartime(&self, shift: u32) -> ConstCtOption<Self> {
        if shift >= Self::BITS {
            return ConstCtOption::none(Self::ZERO);
        }

        // safe to unwrap, due to above check
        let logical_shr = Self(Uint::overflowing_shr_vartime(&self.0, shift).unwrap_or(Uint::ZERO));

        // To turn a logical shr into an arithmetical, the shifted in bits need to match the
        // msb of self.

        let masked_msb = self.bitand(&Self::SIGN_MASK);
        let inverse_shift = shift.saturating_sub(1);
        let shifted_masked_msb = Uint::shr_vartime(&masked_msb.0, inverse_shift);
        let msbs = Self(shifted_masked_msb).negc().0;

        ConstCtOption::some(logical_shr.bitxor(&msbs))
    }

    /// Computes `self >> shift` in a panic-free manner, returning zero if the shift exceeds the
    /// precision.
    pub const fn wrapping_shr(&self, shift: u32) -> Self {
        self.overflowing_shr(shift).unwrap_or(Self::ZERO)
    }

    /// Computes `self >> shift` in variable-time in a panic-free manner, returning zero if the
    /// shift exceeds the precision.
    pub const fn wrapping_shr_vartime(&self, shift: u32) -> Self {
        self.overflowing_shr_vartime(shift).unwrap_or(Self::ZERO)
    }
}

macro_rules! impl_shr {
    ($($shift:ty),+) => {
        $(
            impl<const LIMBS: usize> Shr<$shift> for Int<LIMBS> {
                type Output = Int<LIMBS>;

                #[inline]
                fn shr(self, shift: $shift) -> Int<LIMBS> {
                    <&Self>::shr(&self, shift)
                }
            }

            impl<const LIMBS: usize> Shr<$shift> for &Int<LIMBS> {
                type Output = Int<LIMBS>;

                #[inline]
                fn shr(self, shift: $shift) -> Int<LIMBS> {
                    Int::<LIMBS>::shr(self, u32::try_from(shift).expect("invalid shift"))
                }
            }

            impl<const LIMBS: usize> ShrAssign<$shift> for Int<LIMBS> {
                fn shr_assign(&mut self, shift: $shift) {
                    *self = self.shr(shift)
                }
            }
        )+
    };
}

impl_shr!(i32, u32, usize);

impl<const LIMBS: usize> WrappingShr for Int<LIMBS> {
    fn wrapping_shr(&self, shift: u32) -> Int<LIMBS> {
        self.wrapping_shr(shift)
    }
}

impl<const LIMBS: usize> ShrVartime for Int<LIMBS> {
    fn overflowing_shr_vartime(&self, shift: u32) -> CtOption<Self> {
        self.overflowing_shr(shift).into()
    }
    fn wrapping_shr_vartime(&self, shift: u32) -> Self {
        self.wrapping_shr(shift)
    }
}

#[cfg(test)]
mod tests {
    use core::ops::Div;

    use crate::I256;

    const N: I256 =
        I256::from_be_hex("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141");

    const N_2: I256 =
        I256::from_be_hex("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF5D576E7357A4501DDFE92F46681B20A0");

    #[test]
    fn shr0() {
        assert_eq!(I256::MAX >> 0, I256::MAX);
        assert_eq!(I256::MIN >> 0, I256::MIN);
    }

    #[test]
    fn shr1() {
        assert_eq!(N >> 1, N_2);
    }

    #[test]
    fn shr5() {
        assert_eq!(
            I256::MAX >> 5,
            I256::MAX.div(I256::from(32).to_nz().unwrap()).unwrap()
        );
        assert_eq!(
            I256::MIN >> 5,
            I256::MIN.div(I256::from(32).to_nz().unwrap()).unwrap()
        );
    }

    #[test]
    fn shr7_vartime() {
        assert_eq!(
            I256::MAX.shr_vartime(7),
            I256::MAX.div(I256::from(128).to_nz().unwrap()).unwrap()
        );
        assert_eq!(
            I256::MIN.shr_vartime(7),
            I256::MIN.div(I256::from(128).to_nz().unwrap()).unwrap()
        );
    }

    #[test]
    fn shr256_const() {
        assert!(N.overflowing_shr(256).is_none().is_true_vartime());
        assert!(N.overflowing_shr_vartime(256).is_none().is_true_vartime());
    }

    #[test]
    #[should_panic(expected = "`shift` within the bit size of the integer")]
    fn shr256() {
        let _ = N >> 256;
    }
}
