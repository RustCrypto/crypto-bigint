//! [`UInt`] addition operations.

use crate::{Checked, CheckedMul, Concat, Limb, UInt, Wrapping, Zero};
use core::ops::{Mul, MulAssign};
use subtle::CtOption;

impl<const LIMBS: usize> UInt<LIMBS> {
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
    // TODO(tarcieri): use `concat` (or similar) when const trait is stable
    pub fn mul_wide(&self, rhs: &Self) -> (Self, Self) {
        let zero = Self::ZERO;
        let mut r = [zero.limbs, zero.limbs].concat();
        let mut s = [zero.limbs, zero.limbs, zero.limbs, zero.limbs].concat();

        toom22(&self.limbs, &rhs.limbs, &mut r, &mut s);
        let (lo, hi) = r.split_at(LIMBS);

        (
            Self::new(lo.try_into().unwrap()),
            Self::new(hi.try_into().unwrap()),
        )
    }

    /// Perform saturating multiplication, returning `MAX` on overflow.
    pub fn saturating_mul(&self, rhs: &Self) -> Self {
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
    pub fn wrapping_mul(&self, rhs: &Self) -> Self {
        self.mul_wide(rhs).0
    }

    /// Square self, returning a "wide" result.
    pub fn square(&self) -> <Self as Concat>::Output
    where
        Self: Concat,
    {
        let (lo, hi) = self.mul_wide(self);
        hi.concat(&lo)
    }
}

impl<const LIMBS: usize> CheckedMul<&UInt<LIMBS>> for UInt<LIMBS> {
    type Output = Self;

    fn checked_mul(&self, rhs: &Self) -> CtOption<Self> {
        let (lo, hi) = self.mul_wide(rhs);
        CtOption::new(lo, hi.is_zero())
    }
}

impl<const LIMBS: usize> Mul for Wrapping<UInt<LIMBS>> {
    type Output = Self;

    fn mul(self, rhs: Self) -> Wrapping<UInt<LIMBS>> {
        Wrapping(self.0.wrapping_mul(&rhs.0))
    }
}

impl<const LIMBS: usize> Mul<&Wrapping<UInt<LIMBS>>> for Wrapping<UInt<LIMBS>> {
    type Output = Wrapping<UInt<LIMBS>>;

    fn mul(self, rhs: &Wrapping<UInt<LIMBS>>) -> Wrapping<UInt<LIMBS>> {
        Wrapping(self.0.wrapping_mul(&rhs.0))
    }
}

impl<const LIMBS: usize> Mul<Wrapping<UInt<LIMBS>>> for &Wrapping<UInt<LIMBS>> {
    type Output = Wrapping<UInt<LIMBS>>;

    fn mul(self, rhs: Wrapping<UInt<LIMBS>>) -> Wrapping<UInt<LIMBS>> {
        Wrapping(self.0.wrapping_mul(&rhs.0))
    }
}

impl<const LIMBS: usize> Mul<&Wrapping<UInt<LIMBS>>> for &Wrapping<UInt<LIMBS>> {
    type Output = Wrapping<UInt<LIMBS>>;

    fn mul(self, rhs: &Wrapping<UInt<LIMBS>>) -> Wrapping<UInt<LIMBS>> {
        Wrapping(self.0.wrapping_mul(&rhs.0))
    }
}

impl<const LIMBS: usize> MulAssign for Wrapping<UInt<LIMBS>> {
    fn mul_assign(&mut self, other: Self) {
        *self = *self * other;
    }
}

impl<const LIMBS: usize> MulAssign<&Wrapping<UInt<LIMBS>>> for Wrapping<UInt<LIMBS>> {
    fn mul_assign(&mut self, other: &Self) {
        *self = *self * other;
    }
}

impl<const LIMBS: usize> Mul for Checked<UInt<LIMBS>> {
    type Output = Self;

    fn mul(self, rhs: Self) -> Checked<UInt<LIMBS>> {
        Checked(self.0.and_then(|a| rhs.0.and_then(|b| a.checked_mul(&b))))
    }
}

impl<const LIMBS: usize> Mul<&Checked<UInt<LIMBS>>> for Checked<UInt<LIMBS>> {
    type Output = Checked<UInt<LIMBS>>;

    fn mul(self, rhs: &Checked<UInt<LIMBS>>) -> Checked<UInt<LIMBS>> {
        Checked(self.0.and_then(|a| rhs.0.and_then(|b| a.checked_mul(&b))))
    }
}

impl<const LIMBS: usize> Mul<Checked<UInt<LIMBS>>> for &Checked<UInt<LIMBS>> {
    type Output = Checked<UInt<LIMBS>>;

    fn mul(self, rhs: Checked<UInt<LIMBS>>) -> Checked<UInt<LIMBS>> {
        Checked(self.0.and_then(|a| rhs.0.and_then(|b| a.checked_mul(&b))))
    }
}

impl<const LIMBS: usize> Mul<&Checked<UInt<LIMBS>>> for &Checked<UInt<LIMBS>> {
    type Output = Checked<UInt<LIMBS>>;

    fn mul(self, rhs: &Checked<UInt<LIMBS>>) -> Checked<UInt<LIMBS>> {
        Checked(self.0.and_then(|a| rhs.0.and_then(|b| a.checked_mul(&b))))
    }
}

impl<const LIMBS: usize> MulAssign for Checked<UInt<LIMBS>> {
    fn mul_assign(&mut self, other: Self) {
        *self = *self * other;
    }
}

impl<const LIMBS: usize> MulAssign<&Checked<UInt<LIMBS>>> for Checked<UInt<LIMBS>> {
    fn mul_assign(&mut self, other: &Self) {
        *self = *self * other;
    }
}

// preconditions:
// a.len() == b.len()
// r.len() >= a.len()
// stores the result of |a - b| in the lower a.len() limbs of r
// returns true if a >= b
#[inline(always)]
fn diff_same(a: &[Limb], b: &[Limb], r: &mut [Limb]) -> bool {
    for i in (0..b.len()).rev() {
        if a[i] == b[i] {
            r[i] = Limb::ZERO;
        } else if a[i] > b[i] {
            let mut borrow = Limb::ZERO;
            for j in 0..i + 1 {
                let (w, b) = a[j].sbb(b[j], borrow);
                r[j] = w;
                borrow = b;
            }
            return true;
        } else {
            let mut borrow = Limb::ZERO;
            for j in 0..i + 1 {
                let (w, b) = b[j].sbb(a[j], borrow);
                r[j] = w;
                borrow = b;
            }
            return false;
        }
    }
    true
}

// preconditions:
// a.len() == b.len() || a.len() == b.len() + 1
// if initially toom22 operands have same
// number of limbs then the above condition always holds
// r.len() >= a.len()
// stores the result of |a - b| in the lower a.len() limbs of r
// returns true if a >= b
#[inline(always)]
fn diff(a: &[Limb], b: &[Limb], r: &mut [Limb]) -> bool {
    for i in b.len()..a.len() {
        r[i] = Limb::ZERO;
    }
    if a.len() == b.len() {
        return diff_same(a, b, r);
    } else {
        if a[a.len() - 1] != Limb::ZERO {
            let mut borrow = Limb::ZERO;
            for i in 0..b.len() {
                let (w, b) = a[i].sbb(b[i], borrow);
                r[i] = w;
                borrow = b;
            }

            let (w, _) = a[a.len() - 1].sbb(Limb::ZERO, borrow);
            r[r.len() - 1] = w;
            true
        } else {
            let (a, _) = a.split_at(b.len());
            return diff_same(a, b, r);
        }
    }
}

// input:
// a, b -> numbers to be multiplied given as &[Limb]
// r -> array to store the result
// s -> scratch space used to compute the result
// Output:
// computes a*b and stores result in r
// Preconditions:
// a.len() >= b.len()
// r.len() == a.len() + b.len()
// s.len() == 2*(a.len() + b.len())
pub fn toom22(a: &[Limb], b: &[Limb], r: &mut [Limb], s: &mut [Limb]) {
    let x = a.len() - (a.len() >> 1);

    // use schoolbook multiplication if one of the operands
    // has less than 32 limbs
    if a.len() < 32 {
        for i in 0..r.len() {
            r[i] = Limb::ZERO;
        }
        for i in 0..b.len() {
            let mut carry = Limb::ZERO;
            for j in 0..a.len() {
                let k = i + j;
                let (w, c) = r[k].mac(a[j], b[i], carry);
                r[k] = w;
                carry = c;
            }
            r[i + a.len()] = carry;
        }
    } else {
        // split lower and upper halfs of r
        // rlo => r[0..2x]
        // rhi => r[2x..]
        let (rlo, rhi) = r.split_at_mut(2 * x);

        // split lower half of r to store result of |a0-a1| and |b0-b1|
        let (a_diff, b_diff) = rlo.split_at_mut(x);

        // split lower and upper half of a
        let (a0, a1) = a.split_at(x);

        // split lower and upper half of b
        let (b0, b1) = b.split_at(x);

        // stores whether result of (a0-a1)*(b0-b1) is positive or zero
        let mut is_positive = true;

        // compute |a0-a1| in r[0..x]
        is_positive ^= diff(a0, a1, a_diff);

        // compute |b0-b1| in r[x..2x]
        is_positive ^= diff(b0, b1, b_diff);

        // split scratch space into slo => s[0..2x], shi => s[2x..]
        let (slo, shi) = s.split_at_mut(2 * x);

        // store result of |a0-a1| * |b0-b1| in lower half of s
        // using upper half of s as scratch space
        toom22(a_diff, b_diff, slo, shi);

        // recursively compute multiplication
        // a0*b0 with result in r[0..2x]
        toom22(a0, b0, rlo, shi);

        // a1*b1 with result in r[2x..]
        toom22(a1, b1, rhi, shi);

        // save a0*b0 in the upper half of scratch space
        for i in 0..2 * x {
            shi[i] = rlo[i];
        }

        // denotes final carry left at position 3*x
        let mut cf = Limb::ZERO;

        // carry when a1*b1 is added to r[x..3x]
        let mut c11 = Limb::ZERO;
        for i in x..3 * x {
            let h = if i + x < r.len() {
                r[i + x]
            } else {
                Limb::ZERO
            };
            let (w, c) = r[i].adc(h, c11);
            r[i] = w;
            c11 = c;
        }

        // carry when a0*b0 is added to r[x..3x]
        let mut c00 = Limb::ZERO;
        for i in x..3 * x {
            let (w, c) = r[i].adc(shi[i - x], c00);
            r[i] = w;
            c00 = c;
        }

        // add intermediate carry
        cf = cf.adc(c00, c11).0;

        // if result of (a0-a1)*(b0-b1) is positive we subtract
        // else add to the final result
        match is_positive {
            true => {
                let mut borrow = Limb::ZERO;
                for i in x..3 * x {
                    let (w, b) = r[i].sbb(slo[i - x], borrow);
                    r[i] = w;
                    borrow = b;
                }
                cf = cf.sbb(Limb::ZERO, borrow).0;
            }
            false => {
                let mut carry = Limb::ZERO;
                for i in x..3 * x {
                    let (w, c) = r[i].adc(slo[i - x], carry);
                    r[i] = w;
                    carry = c;
                }
                cf = cf.adc(Limb::ZERO, carry).0;
            }
        }

        // propagate the final carry
        for i in 3 * x..r.len() {
            let (w, c) = r[i].adc(cf, Limb::ZERO);
            r[i] = w;
            if c == Limb::ZERO {
                break;
            }
            cf = c;
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{CheckedMul, Split, Zero, U64};

    #[test]
    fn mul_wide_zero_and_one() {
        assert_eq!(U64::ZERO.mul_wide(&U64::ZERO), (U64::ZERO, U64::ZERO));
        assert_eq!(U64::ZERO.mul_wide(&U64::ONE), (U64::ZERO, U64::ZERO));
        assert_eq!(U64::ONE.mul_wide(&U64::ZERO), (U64::ZERO, U64::ZERO));
        assert_eq!(U64::ONE.mul_wide(&U64::ONE), (U64::ONE, U64::ZERO));
    }

    #[test]
    fn mul_wide_lo_only() {
        let primes: &[u32] = &[3, 5, 17, 256, 65537];

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
}
