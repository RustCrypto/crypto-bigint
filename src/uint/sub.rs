//! [`Uint`] addition operations.

use super::Uint;
use crate::{
    limb::SignedWideWord, Checked, CheckedSub, ConstChoice, Limb, Word, Wrapping, WrappingSub, Zero,
};
use core::ops::{Sub, SubAssign};
use subtle::CtOption;

impl<const LIMBS: usize> Uint<LIMBS> {
    /// Computes `a - (b + borrow)`, returning the result along with the new borrow.
    #[inline(always)]
    pub const fn sbb(&self, rhs: &Self, mut borrow: Limb) -> (Self, Limb) {
        let mut limbs = [Limb::ZERO; LIMBS];
        let mut i = 0;

        while i < LIMBS {
            let (w, b) = self.limbs[i].sbb(rhs.limbs[i], borrow);
            limbs[i] = w;
            borrow = b;
            i += 1;
        }

        (Self { limbs }, borrow)
    }

    /// Perform saturating subtraction, returning `ZERO` on underflow.
    pub const fn saturating_sub(&self, rhs: &Self) -> Self {
        let (res, underflow) = self.sbb(rhs, Limb::ZERO);
        Self::select(&res, &Self::ZERO, ConstChoice::from_word_mask(underflow.0))
    }

    /// Perform wrapping subtraction, discarding underflow and wrapping around
    /// the boundary of the type.
    pub const fn wrapping_sub(&self, rhs: &Self) -> Self {
        self.sbb(rhs, Limb::ZERO).0
    }

    /// Perform wrapping subtraction, returning the truthy value as the second element of the tuple
    /// if an underflow has occurred.
    pub(crate) const fn conditional_wrapping_sub(
        &self,
        rhs: &Self,
        choice: ConstChoice,
    ) -> (Self, ConstChoice) {
        let actual_rhs = Uint::select(&Uint::ZERO, rhs, choice);
        let (res, borrow) = self.sbb(&actual_rhs, Limb::ZERO);
        (res, ConstChoice::from_word_mask(borrow.0))
    }
}

impl<const LIMBS: usize> CheckedSub for Uint<LIMBS> {
    fn checked_sub(&self, rhs: &Self) -> CtOption<Self> {
        let (result, underflow) = self.sbb(rhs, Limb::ZERO);
        CtOption::new(result, underflow.is_zero())
    }
}

impl<const LIMBS: usize> Sub for Uint<LIMBS> {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self {
        self.sub(&rhs)
    }
}

impl<const LIMBS: usize> Sub<&Uint<LIMBS>> for Uint<LIMBS> {
    type Output = Self;

    fn sub(self, rhs: &Self) -> Self {
        self.checked_sub(rhs)
            .expect("attempted to subtract with underflow")
    }
}

impl<const LIMBS: usize> SubAssign for Wrapping<Uint<LIMBS>> {
    fn sub_assign(&mut self, other: Self) {
        *self = *self - other;
    }
}

impl<const LIMBS: usize> SubAssign<&Wrapping<Uint<LIMBS>>> for Wrapping<Uint<LIMBS>> {
    fn sub_assign(&mut self, other: &Self) {
        *self = *self - other;
    }
}

impl<const LIMBS: usize> SubAssign for Checked<Uint<LIMBS>> {
    fn sub_assign(&mut self, other: Self) {
        *self = *self - other;
    }
}

impl<const LIMBS: usize> SubAssign<&Checked<Uint<LIMBS>>> for Checked<Uint<LIMBS>> {
    fn sub_assign(&mut self, other: &Self) {
        *self = *self - other;
    }
}

impl<const LIMBS: usize> WrappingSub for Uint<LIMBS> {
    fn wrapping_sub(&self, v: &Self) -> Self {
        self.wrapping_sub(v)
    }
}

/// Subtract with borrow:
#[inline]
pub(crate) fn sbb(a: Word, b: Word, acc: &mut SignedWideWord) -> Word {
    *acc += a as SignedWideWord;
    *acc -= b as SignedWideWord;
    let lo = *acc as Word;
    *acc >>= Word::BITS;
    lo
}

pub(crate) fn sub2(a: &mut [Limb], b: &[Limb]) {
    let mut borrow = 0;

    let len = core::cmp::min(a.len(), b.len());
    let (a_lo, a_hi) = a.split_at_mut(len);
    let (b_lo, b_hi) = b.split_at(len);

    for (a, b) in a_lo.iter_mut().zip(b_lo) {
        a.0 = sbb(a.0, b.0, &mut borrow);
    }

    if borrow != 0 {
        for a in a_hi {
            a.0 = sbb(a.0, 0, &mut borrow);
            if borrow == 0 {
                break;
            }
        }
    }

    // note: we're _required_ to fail on underflow
    assert!(
        borrow == 0 && b_hi.iter().all(|x| num_traits::Zero::is_zero(x)),
        "Cannot subtract b from a because b is larger than a."
    );
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub(crate) enum Sign {
    Plus,
    Minus,
    NoSign,
}

#[cfg(feature = "alloc")]
pub(crate) fn sub_sign(a: &[Limb], b: &[Limb]) -> (Sign, alloc::vec::Vec<Limb>) {
    use super::cmp::cmp_slice;
    use core::cmp::Ordering;

    match cmp_slice(a, b) {
        Ordering::Greater => {
            let mut a = a.to_vec();
            sub2(&mut a, b);
            (Sign::Plus, a)
        }
        Ordering::Less => {
            let mut b = b.to_vec();
            sub2(&mut b, a);
            (Sign::Minus, b)
        }
        _ => (Sign::NoSign, Default::default()),
    }
}

#[cfg(test)]
mod tests {
    use crate::{CheckedSub, Limb, U128};

    #[test]
    fn sbb_no_borrow() {
        let (res, borrow) = U128::ONE.sbb(&U128::ONE, Limb::ZERO);
        assert_eq!(res, U128::ZERO);
        assert_eq!(borrow, Limb::ZERO);
    }

    #[test]
    fn sbb_with_borrow() {
        let (res, borrow) = U128::ZERO.sbb(&U128::ONE, Limb::ZERO);

        assert_eq!(res, U128::MAX);
        assert_eq!(borrow, Limb::MAX);
    }

    #[test]
    fn saturating_sub_no_borrow() {
        assert_eq!(
            U128::from(5u64).saturating_sub(&U128::ONE),
            U128::from(4u64)
        );
    }

    #[test]
    fn saturating_sub_with_borrow() {
        assert_eq!(
            U128::from(4u64).saturating_sub(&U128::from(5u64)),
            U128::ZERO
        );
    }

    #[test]
    fn wrapping_sub_no_borrow() {
        assert_eq!(U128::ONE.wrapping_sub(&U128::ONE), U128::ZERO);
    }

    #[test]
    fn wrapping_sub_with_borrow() {
        assert_eq!(U128::ZERO.wrapping_sub(&U128::ONE), U128::MAX);
    }

    #[test]
    fn checked_sub_ok() {
        let result = U128::ONE.checked_sub(&U128::ONE);
        assert_eq!(result.unwrap(), U128::ZERO);
    }

    #[test]
    fn checked_sub_overflow() {
        let result = U128::ZERO.checked_sub(&U128::ONE);
        assert!(!bool::from(result.is_some()));
    }
}
