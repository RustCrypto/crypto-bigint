//! [`Uint`] multiplication operations.

use core::ops::{Mul, MulAssign};

use subtle::CtOption;

use crate::{
    Checked, CheckedMul, Concat, ConcatMixed, ConstCtOption, Limb, Uint, WideningMul, Wrapping,
    WrappingMul, Zero,
};

use self::karatsuba::UintKaratsubaMul;

pub(crate) mod karatsuba;

/// Schoolbook multiplication a.k.a. long multiplication, i.e. the traditional method taught in
/// schools.
///
/// The most efficient method for small numbers.
#[inline(always)]
const fn schoolbook_multiplication(lhs: &[Limb], rhs: &[Limb], lo: &mut [Limb], hi: &mut [Limb]) {
    if lhs.len() != lo.len() || rhs.len() != hi.len() {
        panic!("schoolbook multiplication length mismatch");
    }

    let mut i = 0;
    while i < lhs.len() {
        let mut j = 0;
        let mut carry = Limb::ZERO;
        let xi = lhs[i];

        while j < rhs.len() {
            let k = i + j;

            if k >= lhs.len() {
                (hi[k - lhs.len()], carry) = hi[k - lhs.len()].mac(xi, rhs[j], carry);
            } else {
                (lo[k], carry) = lo[k].mac(xi, rhs[j], carry);
            }

            j += 1;
        }

        if i + j >= lhs.len() {
            hi[i + j - lhs.len()] = carry;
        } else {
            lo[i + j] = carry;
        }
        i += 1;
    }
}

/// Schoolbook method of squaring.
///
/// Like schoolbook multiplication, but only considering half of the multiplication grid.
#[inline(always)]
pub(crate) const fn schoolbook_squaring(limbs: &[Limb], lo: &mut [Limb], hi: &mut [Limb]) {
    // Translated from https://github.com/ucbrise/jedi-pairing/blob/c4bf151/include/core/bigint.hpp#L410
    //
    // Permission to relicense the resulting translation as Apache 2.0 + MIT was given
    // by the original author Sam Kumar: https://github.com/RustCrypto/crypto-bigint/pull/133#discussion_r1056870411

    if limbs.len() != lo.len() || lo.len() != hi.len() {
        panic!("schoolbook squaring length mismatch");
    }

    let mut i = 1;
    while i < limbs.len() {
        let mut j = 0;
        let mut carry = Limb::ZERO;
        let xi = limbs[i];

        while j < i {
            let k = i + j;

            if k >= limbs.len() {
                (hi[k - limbs.len()], carry) = hi[k - limbs.len()].mac(xi, limbs[j], carry);
            } else {
                (lo[k], carry) = lo[k].mac(xi, limbs[j], carry);
            }

            j += 1;
        }

        if (2 * i) < limbs.len() {
            lo[2 * i] = carry;
        } else {
            hi[2 * i - limbs.len()] = carry;
        }

        i += 1;
    }

    // Double the current result, this accounts for the other half of the multiplication grid.
    // The top word is empty, so we use a special purpose shl.
    let mut carry = Limb::ZERO;
    let mut i = 0;
    while i < limbs.len() {
        (lo[i].0, carry) = ((lo[i].0 << 1) | carry.0, lo[i].shr(Limb::BITS - 1));
        i += 1;
    }

    let mut i = 0;
    while i < limbs.len() - 1 {
        (hi[i].0, carry) = ((hi[i].0 << 1) | carry.0, hi[i].shr(Limb::BITS - 1));
        i += 1;
    }
    hi[limbs.len() - 1] = carry;

    // Handle the diagonal of the multiplication grid, which finishes the multiplication grid.
    let mut carry = Limb::ZERO;
    let mut i = 0;
    while i < limbs.len() {
        let xi = limbs[i];
        if (i * 2) < limbs.len() {
            (lo[i * 2], carry) = lo[i * 2].mac(xi, xi, carry);
        } else {
            (hi[i * 2 - limbs.len()], carry) = hi[i * 2 - limbs.len()].mac(xi, xi, carry);
        }

        if (i * 2 + 1) < limbs.len() {
            (lo[i * 2 + 1], carry) = lo[i * 2 + 1].overflowing_add(carry);
        } else {
            (hi[i * 2 + 1 - limbs.len()], carry) =
                hi[i * 2 + 1 - limbs.len()].overflowing_add(carry);
        }

        i += 1;
    }
}

impl<const LIMBS: usize> Uint<LIMBS> {
    /// Multiply `self` by `rhs`, returning a concatenated "wide" result.
    pub const fn widening_mul<const RHS_LIMBS: usize, const WIDE_LIMBS: usize>(
        &self,
        rhs: &Uint<RHS_LIMBS>,
    ) -> Uint<WIDE_LIMBS>
    where
        Self: ConcatMixed<Uint<RHS_LIMBS>, MixedOutput = Uint<WIDE_LIMBS>>,
    {
        let (lo, hi) = self.split_mul(rhs);
        Uint::concat_mixed(&lo, &hi)
    }

    /// Compute "wide" multiplication as a 2-tuple containing the `(lo, hi)` components of the product, whose sizes
    /// correspond to the sizes of the operands.
    pub const fn split_mul<const RHS_LIMBS: usize>(
        &self,
        rhs: &Uint<RHS_LIMBS>,
    ) -> (Self, Uint<RHS_LIMBS>) {
        if LIMBS == RHS_LIMBS {
            if LIMBS == 128 {
                let (a, b) = UintKaratsubaMul::<128>::multiply(&self.limbs, &rhs.limbs);
                // resize() should be a no-op, but the compiler can't infer that Uint<LIMBS> is Uint<128>
                return (a.resize(), b.resize());
            }
            if LIMBS == 64 {
                let (a, b) = UintKaratsubaMul::<64>::multiply(&self.limbs, &rhs.limbs);
                return (a.resize(), b.resize());
            }
            if LIMBS == 32 {
                let (a, b) = UintKaratsubaMul::<32>::multiply(&self.limbs, &rhs.limbs);
                return (a.resize(), b.resize());
            }
            if LIMBS == 16 {
                let (a, b) = UintKaratsubaMul::<16>::multiply(&self.limbs, &rhs.limbs);
                return (a.resize(), b.resize());
            }
        }

        uint_mul_limbs(&self.limbs, &rhs.limbs)
    }

    /// Perform wrapping multiplication, discarding overflow.
    pub const fn wrapping_mul<const H: usize>(&self, rhs: &Uint<H>) -> Self {
        self.split_mul(rhs).0
    }

    /// Perform saturating multiplication, returning `MAX` on overflow.
    pub const fn saturating_mul<const RHS_LIMBS: usize>(&self, rhs: &Uint<RHS_LIMBS>) -> Self {
        let (res, overflow) = self.split_mul(rhs);
        Self::select(&res, &Self::MAX, overflow.is_nonzero())
    }
}

/// Squaring operations
impl<const LIMBS: usize> Uint<LIMBS> {
    /// Square self, returning a "wide" result in two parts as (lo, hi).
    pub const fn square_wide(&self) -> (Self, Self) {
        if LIMBS == 128 {
            let (a, b) = UintKaratsubaMul::<128>::square(&self.limbs);
            // resize() should be a no-op, but the compiler can't infer that Uint<LIMBS> is Uint<128>
            return (a.resize(), b.resize());
        }
        if LIMBS == 64 {
            let (a, b) = UintKaratsubaMul::<64>::square(&self.limbs);
            return (a.resize(), b.resize());
        }

        uint_square_limbs(&self.limbs)
    }

    /// Square self, returning a concatenated "wide" result.
    pub const fn widening_square<const WIDE_LIMBS: usize>(&self) -> Uint<WIDE_LIMBS>
    where
        Self: ConcatMixed<Uint<LIMBS>, MixedOutput = Uint<WIDE_LIMBS>>,
    {
        let (lo, hi) = self.square_wide();
        Uint::concat_mixed(&lo, &hi)
    }

    /// Square self, checking that the result fits in the original [`Uint`] size.
    pub const fn checked_square(&self) -> ConstCtOption<Uint<LIMBS>> {
        let (lo, hi) = self.square_wide();
        ConstCtOption::new(lo, Self::eq(&hi, &Self::ZERO))
    }

    /// Perform wrapping square, discarding overflow.
    pub const fn wrapping_square(&self) -> Uint<LIMBS> {
        self.square_wide().0
    }

    /// Perform saturating squaring, returning `MAX` on overflow.
    pub const fn saturating_square(&self) -> Self {
        let (res, overflow) = self.square_wide();
        Self::select(&res, &Self::MAX, overflow.is_nonzero())
    }
}

impl<const LIMBS: usize, const WIDE_LIMBS: usize> Uint<LIMBS>
where
    Self: Concat<Output = Uint<WIDE_LIMBS>>,
{
    /// Square self, returning a concatenated "wide" result.
    pub const fn square(&self) -> Uint<WIDE_LIMBS> {
        let (lo, hi) = self.square_wide();
        lo.concat(&hi)
    }
}

impl<const LIMBS: usize, const RHS_LIMBS: usize> CheckedMul<Uint<RHS_LIMBS>> for Uint<LIMBS> {
    #[inline]
    fn checked_mul(&self, rhs: &Uint<RHS_LIMBS>) -> CtOption<Self> {
        let (lo, hi) = self.split_mul(rhs);
        CtOption::new(lo, hi.is_zero())
    }
}

impl<const LIMBS: usize, const RHS_LIMBS: usize> Mul<Uint<RHS_LIMBS>> for Uint<LIMBS> {
    type Output = Uint<LIMBS>;

    fn mul(self, rhs: Uint<RHS_LIMBS>) -> Self {
        self.mul(&rhs)
    }
}

impl<const LIMBS: usize, const RHS_LIMBS: usize> Mul<&Uint<RHS_LIMBS>> for Uint<LIMBS> {
    type Output = Uint<LIMBS>;

    fn mul(self, rhs: &Uint<RHS_LIMBS>) -> Self {
        (&self).mul(rhs)
    }
}

impl<const LIMBS: usize, const RHS_LIMBS: usize> Mul<Uint<RHS_LIMBS>> for &Uint<LIMBS> {
    type Output = Uint<LIMBS>;

    fn mul(self, rhs: Uint<RHS_LIMBS>) -> Self::Output {
        self.mul(&rhs)
    }
}

impl<const LIMBS: usize, const RHS_LIMBS: usize> Mul<&Uint<RHS_LIMBS>> for &Uint<LIMBS> {
    type Output = Uint<LIMBS>;

    fn mul(self, rhs: &Uint<RHS_LIMBS>) -> Self::Output {
        self.checked_mul(rhs)
            .expect("attempted to multiply with overflow")
    }
}

impl<const LIMBS: usize, const RHS_LIMBS: usize> MulAssign<Uint<RHS_LIMBS>> for Uint<LIMBS> {
    fn mul_assign(&mut self, rhs: Uint<RHS_LIMBS>) {
        *self = self.mul(&rhs)
    }
}

impl<const LIMBS: usize, const RHS_LIMBS: usize> MulAssign<&Uint<RHS_LIMBS>> for Uint<LIMBS> {
    fn mul_assign(&mut self, rhs: &Uint<RHS_LIMBS>) {
        *self = self.mul(rhs)
    }
}

impl<const LIMBS: usize> MulAssign<Wrapping<Uint<LIMBS>>> for Wrapping<Uint<LIMBS>> {
    fn mul_assign(&mut self, other: Wrapping<Uint<LIMBS>>) {
        *self = *self * other;
    }
}

impl<const LIMBS: usize> MulAssign<&Wrapping<Uint<LIMBS>>> for Wrapping<Uint<LIMBS>> {
    fn mul_assign(&mut self, other: &Wrapping<Uint<LIMBS>>) {
        *self = *self * other;
    }
}

impl<const LIMBS: usize> MulAssign<Checked<Uint<LIMBS>>> for Checked<Uint<LIMBS>> {
    fn mul_assign(&mut self, other: Checked<Uint<LIMBS>>) {
        *self = *self * other;
    }
}

impl<const LIMBS: usize> MulAssign<&Checked<Uint<LIMBS>>> for Checked<Uint<LIMBS>> {
    fn mul_assign(&mut self, other: &Checked<Uint<LIMBS>>) {
        *self = *self * other;
    }
}

impl<const LIMBS: usize, const RHS_LIMBS: usize, const WIDE_LIMBS: usize>
    WideningMul<Uint<RHS_LIMBS>> for Uint<LIMBS>
where
    Self: ConcatMixed<Uint<RHS_LIMBS>, MixedOutput = Uint<WIDE_LIMBS>>,
{
    type Output = <Self as ConcatMixed<Uint<RHS_LIMBS>>>::MixedOutput;

    #[inline]
    fn widening_mul(&self, rhs: Uint<RHS_LIMBS>) -> Self::Output {
        self.widening_mul(&rhs)
    }
}

impl<const LIMBS: usize, const RHS_LIMBS: usize, const WIDE_LIMBS: usize>
    WideningMul<&Uint<RHS_LIMBS>> for Uint<LIMBS>
where
    Self: ConcatMixed<Uint<RHS_LIMBS>, MixedOutput = Uint<WIDE_LIMBS>>,
{
    type Output = <Self as ConcatMixed<Uint<RHS_LIMBS>>>::MixedOutput;

    #[inline]
    fn widening_mul(&self, rhs: &Uint<RHS_LIMBS>) -> Self::Output {
        self.widening_mul(rhs)
    }
}

impl<const LIMBS: usize> WrappingMul for Uint<LIMBS> {
    fn wrapping_mul(&self, v: &Self) -> Self {
        self.wrapping_mul(v)
    }
}

/// Helper method to perform schoolbook multiplication
#[inline]
pub(crate) const fn uint_mul_limbs<const LIMBS: usize, const RHS_LIMBS: usize>(
    lhs: &[Limb],
    rhs: &[Limb],
) -> (Uint<LIMBS>, Uint<RHS_LIMBS>) {
    debug_assert!(lhs.len() == LIMBS && rhs.len() == RHS_LIMBS);
    let mut lo: Uint<LIMBS> = Uint::<LIMBS>::ZERO;
    let mut hi = Uint::<RHS_LIMBS>::ZERO;
    schoolbook_multiplication(lhs, rhs, &mut lo.limbs, &mut hi.limbs);
    (lo, hi)
}

/// Helper method to perform schoolbook multiplication
#[inline]
pub(crate) const fn uint_square_limbs<const LIMBS: usize>(
    limbs: &[Limb],
) -> (Uint<LIMBS>, Uint<LIMBS>) {
    let mut lo = Uint::<LIMBS>::ZERO;
    let mut hi = Uint::<LIMBS>::ZERO;
    schoolbook_squaring(limbs, &mut lo.limbs, &mut hi.limbs);
    (lo, hi)
}

/// Wrapper function used by `BoxedUint`
#[cfg(feature = "alloc")]
pub(crate) fn mul_limbs(lhs: &[Limb], rhs: &[Limb], out: &mut [Limb]) {
    debug_assert_eq!(lhs.len() + rhs.len(), out.len());
    let (lo, hi) = out.split_at_mut(lhs.len());
    schoolbook_multiplication(lhs, rhs, lo, hi);
}

/// Wrapper function used by `BoxedUint`
#[cfg(feature = "alloc")]
pub(crate) fn square_limbs(limbs: &[Limb], out: &mut [Limb]) {
    debug_assert_eq!(limbs.len() * 2, out.len());
    let (lo, hi) = out.split_at_mut(limbs.len());
    schoolbook_squaring(limbs, lo, hi);
}

#[cfg(test)]
mod tests {
    use crate::{CheckedMul, ConstChoice, U64, U128, U192, U256, Zero};

    #[test]
    fn mul_wide_zero_and_one() {
        assert_eq!(U64::ZERO.split_mul(&U64::ZERO), (U64::ZERO, U64::ZERO));
        assert_eq!(U64::ZERO.split_mul(&U64::ONE), (U64::ZERO, U64::ZERO));
        assert_eq!(U64::ONE.split_mul(&U64::ZERO), (U64::ZERO, U64::ZERO));
        assert_eq!(U64::ONE.split_mul(&U64::ONE), (U64::ONE, U64::ZERO));
    }

    #[test]
    fn mul_wide_lo_only() {
        let primes: &[u32] = &[3, 5, 17, 257, 65537];

        for &a_int in primes {
            for &b_int in primes {
                let (lo, hi) = U64::from_u32(a_int).split_mul(&U64::from_u32(b_int));
                let expected = U64::from_u64(a_int as u64 * b_int as u64);
                assert_eq!(lo, expected);
                assert!(bool::from(hi.is_zero()));
            }
        }
    }

    #[test]
    fn mul_concat_even() {
        assert_eq!(U64::ZERO.widening_mul(&U64::MAX), U128::ZERO);
        assert_eq!(U64::MAX.widening_mul(&U64::ZERO), U128::ZERO);
        assert_eq!(
            U64::MAX.widening_mul(&U64::MAX),
            U128::from_u128(0xfffffffffffffffe_0000000000000001)
        );
        assert_eq!(
            U64::ONE.widening_mul(&U64::MAX),
            U128::from_u128(0x0000000000000000_ffffffffffffffff)
        );
    }

    #[test]
    fn mul_concat_mixed() {
        let a = U64::from_u64(0x0011223344556677);
        let b = U128::from_u128(0x8899aabbccddeeff_8899aabbccddeeff);
        assert_eq!(a.widening_mul(&b), U192::from(&a).saturating_mul(&b));
        assert_eq!(b.widening_mul(&a), U192::from(&b).saturating_mul(&a));
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
        let (lo, hi) = n.square().split();
        assert_eq!(lo, U64::from_u64(1));
        assert_eq!(hi, U64::from_u64(0xffff_ffff_ffff_fffe));
    }

    #[test]
    fn square_larger() {
        let n = U256::MAX;
        let (lo, hi) = n.square().split();
        assert_eq!(lo, U256::ONE);
        assert_eq!(hi, U256::MAX.wrapping_sub(&U256::ONE));
    }

    #[test]
    fn checked_square() {
        let n = U256::from_u64(u64::MAX).wrapping_add(&U256::ONE);
        let n2 = n.checked_square();
        assert_eq!(n2.is_some(), ConstChoice::TRUE);
        let n4 = n2.unwrap().checked_square();
        assert_eq!(n4.is_none(), ConstChoice::TRUE);
    }

    #[test]
    fn wrapping_square() {
        let n = U256::from_u64(u64::MAX).wrapping_add(&U256::ONE);
        let n2 = n.wrapping_square();
        assert_eq!(n2, U256::from_u128(u128::MAX).wrapping_add(&U256::ONE));
        let n4 = n2.wrapping_square();
        assert_eq!(n4, U256::ZERO);
    }

    #[test]
    fn saturating_square() {
        let n = U256::from_u64(u64::MAX).wrapping_add(&U256::ONE);
        let n2 = n.saturating_square();
        assert_eq!(n2, U256::from_u128(u128::MAX).wrapping_add(&U256::ONE));
        let n4 = n2.saturating_square();
        assert_eq!(n4, U256::MAX);
    }

    #[cfg(feature = "rand_core")]
    #[test]
    fn mul_cmp() {
        use crate::{Random, U4096};
        use rand_core::SeedableRng;
        let mut rng = rand_chacha::ChaCha8Rng::seed_from_u64(1);

        for _ in 0..50 {
            let a = U4096::random(&mut rng);
            assert_eq!(a.split_mul(&a), a.square_wide(), "a = {a}");
        }
    }
}
