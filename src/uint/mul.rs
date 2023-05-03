//! [`Uint`] addition operations.

use crate::{Checked, CheckedMul, Concat, Limb, Uint, WideWord, Word, Wrapping, Zero};
use core::ops::{Mul, MulAssign};
use subtle::CtOption;

impl<const LIMBS: usize> Uint<LIMBS> {
    /// Compute "wide" multiplication, with a product twice the size of the input.
    ///
    /// Returns a tuple containing the `(lo, hi)` components of the product.
    ///
    /// # Ordering note
    ///
    /// Releases of `crypto-bigint` prior to v0.3 used `(hi, lo)` ordering
    /// instead. This has been changed for better consistency with the rest of
    /// the APIs in this crate.
    ///
    /// For more info see: <https://github.com/RustCrypto/crypto-bigint/issues/4>
    // TODO(tarcieri): use `concat` to construct a wide output
    pub const fn mul_wide<const RHS_LIMBS: usize>(
        &self,
        rhs: &Uint<RHS_LIMBS>,
    ) -> (Uint<RHS_LIMBS>, Self) {
        let mut i = 0;
        let mut lo = Uint::<RHS_LIMBS>::ZERO;
        let mut hi = Self::ZERO;

        // Schoolbook multiplication.
        // TODO(tarcieri): use Karatsuba for better performance?
        while i < LIMBS {
            let mut j = 0;
            let mut carry = Limb::ZERO;

            while j < RHS_LIMBS {
                let k = i + j;

                if k >= RHS_LIMBS {
                    let (n, c) = hi.limbs[k - RHS_LIMBS].mac(self.limbs[i], rhs.limbs[j], carry);
                    hi.limbs[k - RHS_LIMBS] = n;
                    carry = c;
                } else {
                    let (n, c) = lo.limbs[k].mac(self.limbs[i], rhs.limbs[j], carry);
                    lo.limbs[k] = n;
                    carry = c;
                }

                j += 1;
            }

            hi.limbs[i + j - RHS_LIMBS] = carry;
            i += 1;
        }

        (lo, hi)
    }

    /// Perform saturating multiplication, returning `MAX` on overflow.
    pub const fn saturating_mul(&self, rhs: &Self) -> Self {
        let (res, overflow) = self.mul_wide(rhs);

        let mut i = 0;
        let mut accumulator = 0;

        while i < LIMBS {
            accumulator |= overflow.limbs[i].0;
            i += 1;
        }

        if accumulator == 0 {
            res
        } else {
            Self::MAX
        }
    }

    /// Perform wrapping multiplication, discarding overflow.
    pub const fn wrapping_mul(&self, rhs: &Self) -> Self {
        self.mul_wide(rhs).0
    }

    /// Square self, returning a concatenated "wide" result.
    pub fn square(&self) -> <Self as Concat>::Output
    where
        Self: Concat,
    {
        let (lo, hi) = self.square_wide();
        hi.concat(&lo)
    }

    /// Square self, returning a "wide" result in two parts as (lo, hi).
    pub const fn square_wide(&self) -> (Self, Self) {
        // Translated from https://github.com/ucbrise/jedi-pairing/blob/c4bf151/include/core/bigint.hpp#L410
        //
        // Permission to relicense the resulting translation as Apache 2.0 + MIT was given
        // by the original author Sam Kumar: https://github.com/RustCrypto/crypto-bigint/pull/133#discussion_r1056870411
        let mut lo = Self::ZERO;
        let mut hi = Self::ZERO;

        // Schoolbook multiplication, but only considering half of the multiplication grid
        let mut i = 1;
        while i < LIMBS {
            let mut j = 0;
            let mut carry = Limb::ZERO;

            while j < i {
                let k = i + j;

                if k >= LIMBS {
                    let (n, c) = hi.limbs[k - LIMBS].mac(self.limbs[i], self.limbs[j], carry);
                    hi.limbs[k - LIMBS] = n;
                    carry = c;
                } else {
                    let (n, c) = lo.limbs[k].mac(self.limbs[i], self.limbs[j], carry);
                    lo.limbs[k] = n;
                    carry = c;
                }

                j += 1;
            }

            if (2 * i) < LIMBS {
                lo.limbs[2 * i] = carry;
            } else {
                hi.limbs[2 * i - LIMBS] = carry;
            }

            i += 1;
        }

        // Double the current result, this accounts for the other half of the multiplication grid.
        // TODO: The top word is empty so we can also use a special purpose shl.
        (lo, hi) = Self::shl_vartime_wide((lo, hi), 1);

        // Handle the diagonal of the multiplication grid, which finishes the multiplication grid.
        let mut carry = Limb::ZERO;
        let mut i = 0;
        while i < LIMBS {
            if (i * 2) < LIMBS {
                let (n, c) = lo.limbs[i * 2].mac(self.limbs[i], self.limbs[i], carry);
                lo.limbs[i * 2] = n;
                carry = c;
            } else {
                let (n, c) = hi.limbs[i * 2 - LIMBS].mac(self.limbs[i], self.limbs[i], carry);
                hi.limbs[i * 2 - LIMBS] = n;
                carry = c;
            }

            if (i * 2 + 1) < LIMBS {
                let n = lo.limbs[i * 2 + 1].0 as WideWord + carry.0 as WideWord;
                lo.limbs[i * 2 + 1] = Limb(n as Word);
                carry = Limb((n >> Word::BITS) as Word);
            } else {
                let n = hi.limbs[i * 2 + 1 - LIMBS].0 as WideWord + carry.0 as WideWord;
                hi.limbs[i * 2 + 1 - LIMBS] = Limb(n as Word);
                carry = Limb((n >> Word::BITS) as Word);
            }

            i += 1;
        }

        (lo, hi)
    }
}

impl<const LIMBS: usize> CheckedMul<&Uint<LIMBS>> for Uint<LIMBS> {
    type Output = Self;

    fn checked_mul(&self, rhs: &Self) -> CtOption<Self> {
        let (lo, hi) = self.mul_wide(rhs);
        CtOption::new(lo, hi.is_zero())
    }
}

impl<const LIMBS: usize> Mul for Wrapping<Uint<LIMBS>> {
    type Output = Self;

    fn mul(self, rhs: Self) -> Wrapping<Uint<LIMBS>> {
        Wrapping(self.0.wrapping_mul(&rhs.0))
    }
}

impl<const LIMBS: usize> Mul<&Wrapping<Uint<LIMBS>>> for Wrapping<Uint<LIMBS>> {
    type Output = Wrapping<Uint<LIMBS>>;

    fn mul(self, rhs: &Wrapping<Uint<LIMBS>>) -> Wrapping<Uint<LIMBS>> {
        Wrapping(self.0.wrapping_mul(&rhs.0))
    }
}

impl<const LIMBS: usize> Mul<Wrapping<Uint<LIMBS>>> for &Wrapping<Uint<LIMBS>> {
    type Output = Wrapping<Uint<LIMBS>>;

    fn mul(self, rhs: Wrapping<Uint<LIMBS>>) -> Wrapping<Uint<LIMBS>> {
        Wrapping(self.0.wrapping_mul(&rhs.0))
    }
}

impl<const LIMBS: usize> Mul<&Wrapping<Uint<LIMBS>>> for &Wrapping<Uint<LIMBS>> {
    type Output = Wrapping<Uint<LIMBS>>;

    fn mul(self, rhs: &Wrapping<Uint<LIMBS>>) -> Wrapping<Uint<LIMBS>> {
        Wrapping(self.0.wrapping_mul(&rhs.0))
    }
}

impl<const LIMBS: usize> MulAssign for Wrapping<Uint<LIMBS>> {
    fn mul_assign(&mut self, other: Self) {
        *self = *self * other;
    }
}

impl<const LIMBS: usize> MulAssign<&Wrapping<Uint<LIMBS>>> for Wrapping<Uint<LIMBS>> {
    fn mul_assign(&mut self, other: &Self) {
        *self = *self * other;
    }
}

impl<const LIMBS: usize> Mul for Checked<Uint<LIMBS>> {
    type Output = Self;

    fn mul(self, rhs: Self) -> Checked<Uint<LIMBS>> {
        Checked(self.0.and_then(|a| rhs.0.and_then(|b| a.checked_mul(&b))))
    }
}

impl<const LIMBS: usize> Mul<&Checked<Uint<LIMBS>>> for Checked<Uint<LIMBS>> {
    type Output = Checked<Uint<LIMBS>>;

    fn mul(self, rhs: &Checked<Uint<LIMBS>>) -> Checked<Uint<LIMBS>> {
        Checked(self.0.and_then(|a| rhs.0.and_then(|b| a.checked_mul(&b))))
    }
}

impl<const LIMBS: usize> Mul<Checked<Uint<LIMBS>>> for &Checked<Uint<LIMBS>> {
    type Output = Checked<Uint<LIMBS>>;

    fn mul(self, rhs: Checked<Uint<LIMBS>>) -> Checked<Uint<LIMBS>> {
        Checked(self.0.and_then(|a| rhs.0.and_then(|b| a.checked_mul(&b))))
    }
}

impl<const LIMBS: usize> Mul<&Checked<Uint<LIMBS>>> for &Checked<Uint<LIMBS>> {
    type Output = Checked<Uint<LIMBS>>;

    fn mul(self, rhs: &Checked<Uint<LIMBS>>) -> Checked<Uint<LIMBS>> {
        Checked(self.0.and_then(|a| rhs.0.and_then(|b| a.checked_mul(&b))))
    }
}

impl<const LIMBS: usize> MulAssign for Checked<Uint<LIMBS>> {
    fn mul_assign(&mut self, other: Self) {
        *self = *self * other;
    }
}

impl<const LIMBS: usize> MulAssign<&Checked<Uint<LIMBS>>> for Checked<Uint<LIMBS>> {
    fn mul_assign(&mut self, other: &Self) {
        *self = *self * other;
    }
}

macro_rules! impl_mul {
    ($(($self_type:ident, $self_bits:expr)),+) => {
        $(
            impl Mul<$self_type> for $self_type {
                type Output = Uint<{nlimbs!($self_bits) * 2}>;

                fn mul(self, rhs: $self_type) -> Uint<{nlimbs!($self_bits) * 2}> {
                    let (lo, hi) = self.mul_wide(&rhs);

                    hi.concat(&lo)
                }
            }

            impl Mul<&$self_type> for $self_type  {
                type Output = Uint<{nlimbs!($self_bits) * 2}>;

                fn mul(self, rhs: &$self_type) -> Uint<{nlimbs!($self_bits) * 2}> {
                    let (lo, hi) = self.mul_wide(rhs);

                    hi.concat(&lo)
                }
            }

            impl Mul<$self_type> for &$self_type  {
                type Output = Uint<{nlimbs!($self_bits) * 2}>;

                fn mul(self, rhs: $self_type) -> Uint<{nlimbs!($self_bits) * 2}> {
                    let (lo, hi) = self.mul_wide(&rhs);

                    hi.concat(&lo)
                }
            }
        )+
    };
}

macro_rules! impl_mul_cross_sizes {
    (($first_type:ident, $first_bits:expr), ($(($second_type:ident, $second_bits:expr)),+ $(,)?)) => {
        $(
            impl Mul<$second_type> for $first_type {
                type Output = Uint<{nlimbs!($first_bits) + nlimbs!($second_bits)}>;

                fn mul(self, rhs: $second_type) -> Uint<{nlimbs!($first_bits) + nlimbs!($second_bits)}> {
                    self.mul_wide(&rhs).into()
                }
            }

            impl Mul<&$second_type> for $first_type  {
                type Output = Uint<{nlimbs!($first_bits) + nlimbs!($second_bits)}>;

                fn mul(self, rhs: &$second_type) -> Uint<{nlimbs!($first_bits) + nlimbs!($second_bits)}> {
                    self.mul_wide(rhs).into()
                }
            }

            impl Mul<$second_type> for &$first_type  {
                type Output = Uint<{nlimbs!($first_bits) + nlimbs!($second_bits)}>;

                fn mul(self, rhs: $second_type) -> Uint<{nlimbs!($first_bits) + nlimbs!($second_bits)}> {
                    self.mul_wide(&rhs).into()
                }
            }

            impl Mul<&$second_type> for &$first_type {
                type Output = Uint<{nlimbs!($first_bits) + nlimbs!($second_bits)}>;

                fn mul(self, rhs: &$second_type) -> Uint<{nlimbs!($first_bits) + nlimbs!($second_bits)}> {
                    self.mul_wide(rhs).into()
                }
            }

            impl Mul<$first_type> for $second_type {
                type Output = Uint<{nlimbs!($second_bits) + nlimbs!($first_bits)}>;

                fn mul(self, rhs: $first_type) -> Uint<{nlimbs!($second_bits) + nlimbs!($first_bits)}> {
                    self.mul_wide(&rhs).into()
                }
            }

            impl Mul<&$first_type> for $second_type  {
                type Output = Uint<{nlimbs!($second_bits) + nlimbs!($first_bits)}>;

                fn mul(self, rhs: &$first_type) -> Uint<{nlimbs!($second_bits) + nlimbs!($first_bits)}> {
                    self.mul_wide(rhs).into()
                }
            }

            impl Mul<$first_type> for &$second_type  {
                type Output = Uint<{nlimbs!($second_bits) + nlimbs!($first_bits)}>;

                fn mul(self, rhs: $first_type) -> Uint<{nlimbs!($second_bits) + nlimbs!($first_bits)}> {
                    self.mul_wide(&rhs).into()
                }
            }

            impl Mul<&$first_type> for &$second_type {
                type Output = Uint<{nlimbs!($second_bits) + nlimbs!($first_bits)}>;

                fn mul(self, rhs: &$first_type) -> Uint<{nlimbs!($second_bits) + nlimbs!($first_bits)}> {
                    self.mul_wide(rhs).into()
                }
            }
        )+
    };
}

#[cfg(test)]
mod tests {
    use crate::{CheckedMul, Zero, U128, U256, U384, U64};

    #[test]
    fn mul_wide_zero_and_one() {
        assert_eq!(U64::ZERO.mul_wide(&U64::ZERO), (U64::ZERO, U64::ZERO));
        assert_eq!(U64::ZERO.mul_wide(&U64::ONE), (U64::ZERO, U64::ZERO));
        assert_eq!(U64::ONE.mul_wide(&U64::ZERO), (U64::ZERO, U64::ZERO));
        assert_eq!(U64::ONE.mul_wide(&U64::ONE), (U64::ONE, U64::ZERO));

        assert_eq!(U128::ZERO.mul_wide(&U256::ZERO), (U256::ZERO, U128::ZERO));
        assert_eq!(U128::ZERO.mul_wide(&U256::ONE), (U256::ZERO, U128::ZERO));
        assert_eq!(U128::ONE.mul_wide(&U256::ZERO), (U256::ZERO, U128::ZERO));
        assert_eq!(U128::ONE.mul_wide(&U256::ONE), (U256::ONE, U128::ZERO));
    }

    #[test]
    fn mul_wide_lo_only() {
        let primes: &[u32] = &[3, 5, 17, 257, 65537];

        for &a_int in primes {
            for &b_int in primes {
                let (lo, hi) = U64::from_u32(a_int).mul_wide(&U64::from_u32(b_int));
                let expected = U64::from_u64(a_int as u64 * b_int as u64);
                assert_eq!(lo, expected);
                assert!(bool::from(hi.is_zero()));
            }
        }
    }

    #[test]
    fn checked_mul_ok() {
        let n = U64::from_u32(0xffff_ffff);
        assert_eq!(
            n.checked_mul(&n).unwrap(),
            U64::from_u64(0xffff_fffe_0000_0001)
        );
    }

    #[test]
    fn checked_mul_overflow() {
        let n = U64::from_u64(0xffff_ffff_ffff_ffff);
        assert!(bool::from(n.checked_mul(&n).is_none()));
    }

    #[test]
    fn saturating_mul_no_overflow() {
        let n = U64::from_u8(8);
        assert_eq!(n.saturating_mul(&n), U64::from_u8(64));
    }

    #[test]
    fn saturating_mul_overflow() {
        let a = U64::from(0xffff_ffff_ffff_ffffu64);
        let b = U64::from(2u8);
        assert_eq!(a.saturating_mul(&b), U64::MAX);
    }

    #[test]
    fn square() {
        let n = U64::from_u64(0xffff_ffff_ffff_ffff);
        let (hi, lo) = n.square().split();
        assert_eq!(lo, U64::from_u64(1));
        assert_eq!(hi, U64::from_u64(0xffff_ffff_ffff_fffe));
    }

    #[test]
    fn square_larger() {
        let n = U256::MAX;
        let (hi, lo) = n.square().split();
        assert_eq!(lo, U256::ONE);
        assert_eq!(hi, U256::MAX.wrapping_sub(&U256::ONE));
    }

    #[test]
    fn mul_wide_cross_sizes() {
        let x = U128::from_be_hex("ffffffffffffffffffffffffffffffff");
        let y =
            U256::from_be_hex("0fffffffffffffffffffffafffffffffffffffffffffffffffffffffffffffff");
        let (lo, hi) = x.mul_wide(&y);

        assert_eq!(
            lo,
            U256::from_be_hex("f0000000000000000000004fffffffff00000000000000000000000000000001")
        );

        assert_eq!(hi, U128::from_be_hex("0fffffffffffffffffffffafffffffff"));
    }

    #[test]
    fn mul() {
        let x = U128::from_be_hex("ffffffffffffffffffffffffffffffff");
        let y = U128::from_be_hex("0fffffffffffffffffffffafffffffff");
        let xy: U256 = x.mul_wide(&y).into();

        assert_eq!(xy, x * y);

        assert_eq!(
            xy,
            U256::from_be_hex("0fffffffffffffffffffffaffffffffef0000000000000000000005000000001")
        );
    }

    #[test]
    fn mul_cross_sizes() {
        let x = U128::from_be_hex("ffffffffffffffffffffffffffffffff");
        let y =
            U256::from_be_hex("0fffffffffffffffffffffafffffffffffffffffffffffffffffffffffffffff");
        let xy: U384 = x.mul_wide(&y).into();

        assert_eq!(xy, x * y);
        assert_eq!(xy, y * x);

        assert_eq!(
            xy,
            U384::from_be_hex("0fffffffffffffffffffffaffffffffff0000000000000000000004fffffffff00000000000000000000000000000001")
        );
    }
}
