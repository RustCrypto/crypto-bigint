//! [`Uint`] division operations.

use super::div_limb::{div_rem_limb_with_reciprocal, Reciprocal};
use super::Uint;
use crate::limb::Word;
use crate::{Integer, Limb, NonZero, Wrapping};
use core::ops::{Div, DivAssign, Rem, RemAssign};
use subtle::{Choice, CtOption};

impl<const LIMBS: usize> Uint<LIMBS> {
    /// Computes `self` / `rhs` using a pre-made reciprocal,
    /// returns the quotient (q) and remainder (r).
    pub const fn ct_div_rem_limb_with_reciprocal(&self, reciprocal: &Reciprocal) -> (Self, Limb) {
        div_rem_limb_with_reciprocal(self, reciprocal)
    }

    /// Computes `self` / `rhs` using a pre-made reciprocal,
    /// returns the quotient (q) and remainder (r).
    pub fn div_rem_limb_with_reciprocal(
        &self,
        reciprocal: &CtOption<Reciprocal>,
    ) -> CtOption<(Self, Limb)> {
        reciprocal.map(|r| div_rem_limb_with_reciprocal(self, &r))
    }

    /// Computes `self` / `rhs`, returns the quotient (q) and remainder (r).
    pub fn ct_div_rem_limb(&self, rhs: Limb) -> (Self, Limb, u8) {
        let (reciprocal, is_some) = Reciprocal::new_const(rhs);
        let (quo, rem) = div_rem_limb_with_reciprocal(self, &reciprocal);
        (quo, rem, is_some)
    }

    /// Computes `self` / `rhs`, returns the quotient (q) and remainder (r).
    pub fn div_rem_limb(&self, rhs: NonZero<Limb>) -> (Self, Limb) {
        let (quo, rem, is_some) = self.ct_div_rem_limb(*rhs);
        // Guaranteed to succeed since `rhs` is nonzero.
        debug_assert!(is_some == 1);
        (quo, rem)
    }

    /// Computes `self` / `rhs`, returns the quotient (q).
    pub fn div_limb(&self, rhs: NonZero<Limb>) -> Self {
        let (q, _r) = self.div_rem_limb(rhs);
        q
    }

    /// Computes `self` / `rhs`, returns the remainder (r).
    pub fn rem_limb(&self, rhs: NonZero<Limb>) -> Limb {
        let (_q, r) = self.div_rem_limb(rhs);
        r
    }

    /// Computes `self` / `rhs`, returns the quotient (q), remainder (r)
    /// and 1 for is_some or 0 for is_none. The results can be wrapped in [`CtOption`].
    /// NOTE: Use only if you need to access const fn. Otherwise use `div_rem` because
    /// the value for is_some needs to be checked before using `q` and `r`.
    ///
    /// This is variable only with respect to `rhs`.
    ///
    /// When used with a fixed `rhs`, this function is constant-time with respect
    /// to `self`.
    pub(crate) const fn ct_div_rem(&self, rhs: &Self) -> (Self, Self, u8) {
        let mb = rhs.bits_vartime();
        let mut bd = (LIMBS * Limb::BIT_SIZE) - mb;
        let mut rem = *self;
        let mut quo = Self::ZERO;
        let mut c = rhs.shl_vartime(bd);

        loop {
            let (mut r, borrow) = rem.sbb(&c, Limb::ZERO);
            rem = Self::ct_select(r, rem, borrow.0);
            r = quo.bitor(&Self::ONE);
            quo = Self::ct_select(r, quo, borrow.0);
            if bd == 0 {
                break;
            }
            bd -= 1;
            c = c.shr_vartime(1);
            quo = quo.shl_vartime(1);
        }

        let is_some = Limb(mb as Word).is_nonzero();
        quo = Self::ct_select(Self::ZERO, quo, is_some);
        (quo, rem, (is_some & 1) as u8)
    }

    /// Computes `self` % `rhs`, returns the remainder and
    /// and 1 for is_some or 0 for is_none. The results can be wrapped in [`CtOption`].
    /// NOTE: Use only if you need to access const fn. Otherwise use `reduce`
    /// This is variable only with respect to `rhs`.
    ///
    /// When used with a fixed `rhs`, this function is constant-time with respect
    /// to `self`.
    pub(crate) const fn ct_reduce(&self, rhs: &Self) -> (Self, u8) {
        let mb = rhs.bits_vartime();
        let mut bd = (LIMBS * Limb::BIT_SIZE) - mb;
        let mut rem = *self;
        let mut c = rhs.shl_vartime(bd);

        loop {
            let (r, borrow) = rem.sbb(&c, Limb::ZERO);
            rem = Self::ct_select(r, rem, borrow.0);
            if bd == 0 {
                break;
            }
            bd -= 1;
            c = c.shr_vartime(1);
        }

        let is_some = Limb(mb as Word).is_nonzero();
        (rem, (is_some & 1) as u8)
    }

    /// Computes `self` % `rhs`, returns the remainder and
    /// and 1 for is_some or 0 for is_none. The results can be wrapped in [`CtOption`].
    /// NOTE: Use only if you need to access const fn. Otherwise use `reduce`
    /// This is variable only with respect to `rhs`.
    ///
    /// When used with a fixed `rhs`, this function is constant-time with respect
    /// to `self`.
    #[allow(dead_code)]
    pub(crate) const fn ct_reduce_wide(lower_upper: (Self, Self), rhs: &Self) -> (Self, u8) {
        let mb = rhs.bits_vartime();

        // The number of bits to consider is two sets of limbs * BIT_SIZE - mb (modulus bitcount)
        let mut bd = (2 * LIMBS * Limb::BIT_SIZE) - mb;

        // The wide integer to reduce, split into two halves
        let (mut lower, mut upper) = lower_upper;

        // Factor of the modulus, split into two halves
        let mut c = Self::shl_vartime_wide((*rhs, Uint::ZERO), bd);

        loop {
            let (lower_sub, borrow) = lower.sbb(&c.0, Limb::ZERO);
            let (upper_sub, borrow) = upper.sbb(&c.1, borrow);

            lower = Self::ct_select(lower_sub, lower, borrow.0);
            upper = Self::ct_select(upper_sub, upper, borrow.0);
            if bd == 0 {
                break;
            }
            bd -= 1;
            c = Self::shr_vartime_wide(c, 1);
        }

        let is_some = Limb(mb as Word).is_nonzero();
        (lower, (is_some & 1) as u8)
    }

    /// Computes `self` % 2^k. Faster than reduce since its a power of 2.
    /// Limited to 2^16-1 since Uint doesn't support higher.
    pub const fn reduce2k(&self, k: usize) -> Self {
        let highest = (LIMBS - 1) as u32;
        let index = k as u32 / (Limb::BIT_SIZE as u32);
        let res = Limb::ct_cmp(Limb::from_u32(index), Limb::from_u32(highest)) - 1;
        let le = Limb::is_nonzero(Limb(res as Word));
        let word = Limb::ct_select(Limb::from_u32(highest), Limb::from_u32(index), le).0 as usize;

        let base = k % Limb::BIT_SIZE;
        let mask = (1 << base) - 1;
        let mut out = *self;

        let outmask = Limb(out.limbs[word].0 & mask);

        out.limbs[word] = Limb::ct_select(out.limbs[word], outmask, le);

        let mut i = word + 1;
        while i < LIMBS {
            out.limbs[i] = Limb::ZERO;
            i += 1;
        }

        out
    }

    /// Computes self / rhs, returns the quotient, remainder
    /// if rhs != 0
    pub fn div_rem(&self, rhs: &Self) -> CtOption<(Self, Self)> {
        let (q, r, c) = self.ct_div_rem(rhs);
        CtOption::new((q, r), Choice::from(c))
    }

    /// Computes self % rhs, returns the remainder
    /// if rhs != 0
    pub fn reduce(&self, rhs: &Self) -> CtOption<Self> {
        let (r, c) = self.ct_reduce(rhs);
        CtOption::new(r, Choice::from(c))
    }

    /// Wrapped division is just normal division i.e. `self` / `rhs`
    /// There’s no way wrapping could ever happen.
    /// This function exists, so that all operations are accounted for in the wrapping operations.
    pub const fn wrapping_div(&self, rhs: &Self) -> Self {
        let (q, _, c) = self.ct_div_rem(rhs);
        assert!(c == 1, "divide by zero");
        q
    }

    /// Perform checked division, returning a [`CtOption`] which `is_some`
    /// only if the rhs != 0
    pub fn checked_div(&self, rhs: &Self) -> CtOption<Self> {
        let (q, _, c) = self.ct_div_rem(rhs);
        CtOption::new(q, Choice::from(c))
    }

    /// Wrapped (modular) remainder calculation is just `self` % `rhs`.
    /// There’s no way wrapping could ever happen.
    /// This function exists, so that all operations are accounted for in the wrapping operations.
    pub const fn wrapping_rem(&self, rhs: &Self) -> Self {
        let (r, c) = self.ct_reduce(rhs);
        assert!(c == 1, "modulo zero");
        r
    }

    /// Perform checked reduction, returning a [`CtOption`] which `is_some`
    /// only if the rhs != 0
    pub fn checked_rem(&self, rhs: &Self) -> CtOption<Self> {
        let (r, c) = self.ct_reduce(rhs);
        CtOption::new(r, Choice::from(c))
    }
}

//
// Division by a single limb
//

impl<const LIMBS: usize> Div<&NonZero<Limb>> for &Uint<LIMBS> {
    type Output = Uint<LIMBS>;

    fn div(self, rhs: &NonZero<Limb>) -> Self::Output {
        *self / *rhs
    }
}

impl<const LIMBS: usize> Div<&NonZero<Limb>> for Uint<LIMBS> {
    type Output = Uint<LIMBS>;

    fn div(self, rhs: &NonZero<Limb>) -> Self::Output {
        self / *rhs
    }
}

impl<const LIMBS: usize> Div<NonZero<Limb>> for &Uint<LIMBS> {
    type Output = Uint<LIMBS>;

    fn div(self, rhs: NonZero<Limb>) -> Self::Output {
        *self / rhs
    }
}

impl<const LIMBS: usize> Div<NonZero<Limb>> for Uint<LIMBS> {
    type Output = Uint<LIMBS>;

    fn div(self, rhs: NonZero<Limb>) -> Self::Output {
        let (q, _, _) = self.ct_div_rem_limb(*rhs);
        q
    }
}

impl<const LIMBS: usize> DivAssign<&NonZero<Limb>> for Uint<LIMBS>
{
    fn div_assign(&mut self, rhs: &NonZero<Limb>) {
        *self /= *rhs;
    }
}

impl<const LIMBS: usize> DivAssign<NonZero<Limb>> for Uint<LIMBS>
{
    fn div_assign(&mut self, rhs: NonZero<Limb>) {
        *self = *self / rhs;
    }
}

impl<const LIMBS: usize> Div<NonZero<Limb>> for Wrapping<Uint<LIMBS>> {
    type Output = Wrapping<Uint<LIMBS>>;

    fn div(self, rhs: NonZero<Limb>) -> Self::Output {
        Wrapping(self.0 / rhs)
    }
}

impl<const LIMBS: usize> Div<NonZero<Limb>> for &Wrapping<Uint<LIMBS>> {
    type Output = Wrapping<Uint<LIMBS>>;

    fn div(self, rhs: NonZero<Limb>) -> Self::Output {
        *self / rhs
    }
}

impl<const LIMBS: usize> Div<&NonZero<Limb>> for &Wrapping<Uint<LIMBS>> {
    type Output = Wrapping<Uint<LIMBS>>;

    fn div(self, rhs: &NonZero<Limb>) -> Self::Output {
        *self / *rhs
    }
}

impl<const LIMBS: usize> Div<&NonZero<Limb>> for Wrapping<Uint<LIMBS>> {
    type Output = Wrapping<Uint<LIMBS>>;

    fn div(self, rhs: &NonZero<Limb>) -> Self::Output {
        self / *rhs
    }
}

impl<const LIMBS: usize> DivAssign<&NonZero<Limb>> for Wrapping<Uint<LIMBS>> {
    fn div_assign(&mut self, rhs: &NonZero<Limb>) {
        *self = Wrapping(self.0 / rhs)
    }
}

impl<const LIMBS: usize> DivAssign<NonZero<Limb>> for Wrapping<Uint<LIMBS>> {
    fn div_assign(&mut self, rhs: NonZero<Limb>) {
        *self /= &rhs;
    }
}

impl<const LIMBS: usize> Rem<&NonZero<Limb>> for &Uint<LIMBS> {
    type Output = Limb;

    fn rem(self, rhs: &NonZero<Limb>) -> Self::Output {
        *self % *rhs
    }
}

impl<const LIMBS: usize> Rem<&NonZero<Limb>> for Uint<LIMBS> {
    type Output = Limb;

    fn rem(self, rhs: &NonZero<Limb>) -> Self::Output {
        self % *rhs
    }
}

impl<const LIMBS: usize> Rem<NonZero<Limb>> for &Uint<LIMBS> {
    type Output = Limb;

    fn rem(self, rhs: NonZero<Limb>) -> Self::Output {
        *self % rhs
    }
}

impl<const LIMBS: usize> Rem<NonZero<Limb>> for Uint<LIMBS> {
    type Output = Limb;

    fn rem(self, rhs: NonZero<Limb>) -> Self::Output {
        let (_, r, _) = self.ct_div_rem_limb(*rhs);
        r
    }
}

impl<const LIMBS: usize> RemAssign<&NonZero<Limb>> for Uint<LIMBS> {
    fn rem_assign(&mut self, rhs: &NonZero<Limb>) {
        *self = (*self % rhs).into();
    }
}

impl<const LIMBS: usize> RemAssign<NonZero<Limb>> for Uint<LIMBS> {
    fn rem_assign(&mut self, rhs: NonZero<Limb>) {
        *self %= &rhs;
    }
}

impl<const LIMBS: usize> Rem<NonZero<Limb>> for Wrapping<Uint<LIMBS>> {
    type Output = Wrapping<Limb>;

    fn rem(self, rhs: NonZero<Limb>) -> Self::Output {
        Wrapping(self.0 % rhs)
    }
}

impl<const LIMBS: usize> Rem<NonZero<Limb>> for &Wrapping<Uint<LIMBS>> {
    type Output = Wrapping<Limb>;

    fn rem(self, rhs: NonZero<Limb>) -> Self::Output {
        *self % rhs
    }
}

impl<const LIMBS: usize> Rem<&NonZero<Limb>> for &Wrapping<Uint<LIMBS>> {
    type Output = Wrapping<Limb>;

    fn rem(self, rhs: &NonZero<Limb>) -> Self::Output {
        *self % *rhs
    }
}

impl<const LIMBS: usize> Rem<&NonZero<Limb>> for Wrapping<Uint<LIMBS>> {
    type Output = Wrapping<Limb>;

    fn rem(self, rhs: &NonZero<Limb>) -> Self::Output {
        self % *rhs
    }
}

impl<const LIMBS: usize> RemAssign<NonZero<Limb>> for Wrapping<Uint<LIMBS>> {
    fn rem_assign(&mut self, rhs: NonZero<Limb>) {
        *self %= &rhs;
    }
}

impl<const LIMBS: usize> RemAssign<&NonZero<Limb>> for Wrapping<Uint<LIMBS>> {
    fn rem_assign(&mut self, rhs: &NonZero<Limb>) {
        *self = Wrapping((self.0 % rhs).into())
    }
}

//
// Division by an Uint
//

impl<const LIMBS: usize> Div<&NonZero<Uint<LIMBS>>> for &Uint<LIMBS>
where
    Uint<LIMBS>: Integer,
{
    type Output = Uint<LIMBS>;

    fn div(self, rhs: &NonZero<Uint<LIMBS>>) -> Self::Output {
        *self / *rhs
    }
}

impl<const LIMBS: usize> Div<&NonZero<Uint<LIMBS>>> for Uint<LIMBS>
where
    Uint<LIMBS>: Integer,
{
    type Output = Uint<LIMBS>;

    fn div(self, rhs: &NonZero<Uint<LIMBS>>) -> Self::Output {
        self / *rhs
    }
}

impl<const LIMBS: usize> Div<NonZero<Uint<LIMBS>>> for &Uint<LIMBS>
where
    Uint<LIMBS>: Integer,
{
    type Output = Uint<LIMBS>;

    fn div(self, rhs: NonZero<Uint<LIMBS>>) -> Self::Output {
        *self / rhs
    }
}

impl<const LIMBS: usize> Div<NonZero<Uint<LIMBS>>> for Uint<LIMBS>
where
    Uint<LIMBS>: Integer,
{
    type Output = Uint<LIMBS>;

    fn div(self, rhs: NonZero<Uint<LIMBS>>) -> Self::Output {
        let (q, _, _) = self.ct_div_rem(&rhs);
        q
    }
}

impl<const LIMBS: usize> DivAssign<&NonZero<Uint<LIMBS>>> for Uint<LIMBS>
where
    Uint<LIMBS>: Integer,
{
    fn div_assign(&mut self, rhs: &NonZero<Uint<LIMBS>>) {
        let (q, _, _) = self.ct_div_rem(rhs);
        *self = q
    }
}

impl<const LIMBS: usize> DivAssign<NonZero<Uint<LIMBS>>> for Uint<LIMBS>
where
    Uint<LIMBS>: Integer,
{
    fn div_assign(&mut self, rhs: NonZero<Uint<LIMBS>>) {
        *self /= &rhs;
    }
}

impl<const LIMBS: usize> Div<NonZero<Uint<LIMBS>>> for Wrapping<Uint<LIMBS>> {
    type Output = Wrapping<Uint<LIMBS>>;

    fn div(self, rhs: NonZero<Uint<LIMBS>>) -> Self::Output {
        Wrapping(self.0.wrapping_div(rhs.as_ref()))
    }
}

impl<const LIMBS: usize> Div<NonZero<Uint<LIMBS>>> for &Wrapping<Uint<LIMBS>> {
    type Output = Wrapping<Uint<LIMBS>>;

    fn div(self, rhs: NonZero<Uint<LIMBS>>) -> Self::Output {
        *self / rhs
    }
}

impl<const LIMBS: usize> Div<&NonZero<Uint<LIMBS>>> for &Wrapping<Uint<LIMBS>> {
    type Output = Wrapping<Uint<LIMBS>>;

    fn div(self, rhs: &NonZero<Uint<LIMBS>>) -> Self::Output {
        *self / *rhs
    }
}

impl<const LIMBS: usize> Div<&NonZero<Uint<LIMBS>>> for Wrapping<Uint<LIMBS>> {
    type Output = Wrapping<Uint<LIMBS>>;

    fn div(self, rhs: &NonZero<Uint<LIMBS>>) -> Self::Output {
        self / *rhs
    }
}

impl<const LIMBS: usize> DivAssign<&NonZero<Uint<LIMBS>>> for Wrapping<Uint<LIMBS>> {
    fn div_assign(&mut self, rhs: &NonZero<Uint<LIMBS>>) {
        *self = Wrapping(self.0.wrapping_div(rhs.as_ref()))
    }
}

impl<const LIMBS: usize> DivAssign<NonZero<Uint<LIMBS>>> for Wrapping<Uint<LIMBS>> {
    fn div_assign(&mut self, rhs: NonZero<Uint<LIMBS>>) {
        *self /= &rhs;
    }
}

impl<const LIMBS: usize> Rem<&NonZero<Uint<LIMBS>>> for &Uint<LIMBS>
where
    Uint<LIMBS>: Integer,
{
    type Output = Uint<LIMBS>;

    fn rem(self, rhs: &NonZero<Uint<LIMBS>>) -> Self::Output {
        *self % *rhs
    }
}

impl<const LIMBS: usize> Rem<&NonZero<Uint<LIMBS>>> for Uint<LIMBS>
where
    Uint<LIMBS>: Integer,
{
    type Output = Uint<LIMBS>;

    fn rem(self, rhs: &NonZero<Uint<LIMBS>>) -> Self::Output {
        self % *rhs
    }
}

impl<const LIMBS: usize> Rem<NonZero<Uint<LIMBS>>> for &Uint<LIMBS>
where
    Uint<LIMBS>: Integer,
{
    type Output = Uint<LIMBS>;

    fn rem(self, rhs: NonZero<Uint<LIMBS>>) -> Self::Output {
        *self % rhs
    }
}

impl<const LIMBS: usize> Rem<NonZero<Uint<LIMBS>>> for Uint<LIMBS>
where
    Uint<LIMBS>: Integer,
{
    type Output = Uint<LIMBS>;

    fn rem(self, rhs: NonZero<Uint<LIMBS>>) -> Self::Output {
        let (r, _) = self.ct_reduce(&rhs);
        r
    }
}

impl<const LIMBS: usize> RemAssign<&NonZero<Uint<LIMBS>>> for Uint<LIMBS>
where
    Uint<LIMBS>: Integer,
{
    fn rem_assign(&mut self, rhs: &NonZero<Uint<LIMBS>>) {
        let (r, _) = self.ct_reduce(rhs);
        *self = r
    }
}

impl<const LIMBS: usize> RemAssign<NonZero<Uint<LIMBS>>> for Uint<LIMBS>
where
    Uint<LIMBS>: Integer,
{
    fn rem_assign(&mut self, rhs: NonZero<Uint<LIMBS>>) {
        *self %= &rhs;
    }
}

impl<const LIMBS: usize> Rem<NonZero<Uint<LIMBS>>> for Wrapping<Uint<LIMBS>> {
    type Output = Wrapping<Uint<LIMBS>>;

    fn rem(self, rhs: NonZero<Uint<LIMBS>>) -> Self::Output {
        Wrapping(self.0.wrapping_rem(rhs.as_ref()))
    }
}

impl<const LIMBS: usize> Rem<NonZero<Uint<LIMBS>>> for &Wrapping<Uint<LIMBS>> {
    type Output = Wrapping<Uint<LIMBS>>;

    fn rem(self, rhs: NonZero<Uint<LIMBS>>) -> Self::Output {
        *self % rhs
    }
}

impl<const LIMBS: usize> Rem<&NonZero<Uint<LIMBS>>> for &Wrapping<Uint<LIMBS>> {
    type Output = Wrapping<Uint<LIMBS>>;

    fn rem(self, rhs: &NonZero<Uint<LIMBS>>) -> Self::Output {
        *self % *rhs
    }
}

impl<const LIMBS: usize> Rem<&NonZero<Uint<LIMBS>>> for Wrapping<Uint<LIMBS>> {
    type Output = Wrapping<Uint<LIMBS>>;

    fn rem(self, rhs: &NonZero<Uint<LIMBS>>) -> Self::Output {
        self % *rhs
    }
}

impl<const LIMBS: usize> RemAssign<NonZero<Uint<LIMBS>>> for Wrapping<Uint<LIMBS>> {
    fn rem_assign(&mut self, rhs: NonZero<Uint<LIMBS>>) {
        *self %= &rhs;
    }
}

impl<const LIMBS: usize> RemAssign<&NonZero<Uint<LIMBS>>> for Wrapping<Uint<LIMBS>> {
    fn rem_assign(&mut self, rhs: &NonZero<Uint<LIMBS>>) {
        *self = Wrapping(self.0.wrapping_rem(rhs.as_ref()))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{limb::HI_BIT, Limb, U256};

    #[cfg(feature = "rand")]
    use {
        crate::{CheckedMul, Random},
        rand_chacha::ChaChaRng,
        rand_core::RngCore,
        rand_core::SeedableRng,
    };

    #[test]
    fn div_word() {
        for (n, d, e, ee) in &[
            (200u64, 2u64, 100u64, 0),
            (100u64, 25u64, 4u64, 0),
            (100u64, 10u64, 10u64, 0),
            (1024u64, 8u64, 128u64, 0),
            (27u64, 13u64, 2u64, 1u64),
            (26u64, 13u64, 2u64, 0u64),
            (14u64, 13u64, 1u64, 1u64),
            (13u64, 13u64, 1u64, 0u64),
            (12u64, 13u64, 0u64, 12u64),
            (1u64, 13u64, 0u64, 1u64),
        ] {
            let lhs = U256::from(*n);
            let rhs = U256::from(*d);
            let (q, r, is_some) = lhs.ct_div_rem(&rhs);
            assert_eq!(is_some, 1);
            assert_eq!(U256::from(*e), q);
            assert_eq!(U256::from(*ee), r);
        }
    }

    #[cfg(feature = "rand")]
    #[test]
    fn div() {
        let mut rng = ChaChaRng::from_seed([7u8; 32]);
        for _ in 0..25 {
            let num = U256::random(&mut rng).shr_vartime(128);
            let den = U256::random(&mut rng).shr_vartime(128);
            let n = num.checked_mul(&den);
            if n.is_some().unwrap_u8() == 1 {
                let (q, _, is_some) = n.unwrap().ct_div_rem(&den);
                assert_eq!(is_some, 1);
                assert_eq!(q, num);
            }
        }
    }

    #[test]
    fn div_max() {
        let mut a = U256::ZERO;
        let mut b = U256::ZERO;
        b.limbs[b.limbs.len() - 1] = Limb(Word::MAX);
        let q = a.wrapping_div(&b);
        assert_eq!(q, Uint::ZERO);
        a.limbs[a.limbs.len() - 1] = Limb(1 << (HI_BIT - 7));
        b.limbs[b.limbs.len() - 1] = Limb(0x82 << (HI_BIT - 7));
        let q = a.wrapping_div(&b);
        assert_eq!(q, Uint::ZERO);
    }

    #[test]
    fn div_zero() {
        let (q, r, is_some) = U256::ONE.ct_div_rem(&U256::ZERO);
        assert_eq!(is_some, 0);
        assert_eq!(q, U256::ZERO);
        assert_eq!(r, U256::ONE);
    }

    #[test]
    fn div_one() {
        let (q, r, is_some) = U256::from(10u8).ct_div_rem(&U256::ONE);
        assert_eq!(is_some, 1);
        assert_eq!(q, U256::from(10u8));
        assert_eq!(r, U256::ZERO);
    }

    #[test]
    fn reduce_one() {
        let (r, is_some) = U256::from(10u8).ct_reduce(&U256::ONE);
        assert_eq!(is_some, 1);
        assert_eq!(r, U256::ZERO);
    }

    #[test]
    fn reduce_zero() {
        let u = U256::from(10u8);
        let (r, is_some) = u.ct_reduce(&U256::ZERO);
        assert_eq!(is_some, 0);
        assert_eq!(r, u);
    }

    #[test]
    fn reduce_tests() {
        let (r, is_some) = U256::from(10u8).ct_reduce(&U256::from(2u8));
        assert_eq!(is_some, 1);
        assert_eq!(r, U256::ZERO);
        let (r, is_some) = U256::from(10u8).ct_reduce(&U256::from(3u8));
        assert_eq!(is_some, 1);
        assert_eq!(r, U256::ONE);
        let (r, is_some) = U256::from(10u8).ct_reduce(&U256::from(7u8));
        assert_eq!(is_some, 1);
        assert_eq!(r, U256::from(3u8));
    }

    #[test]
    fn reduce_tests_wide_zero_padded() {
        let (r, is_some) = U256::ct_reduce_wide((U256::from(10u8), U256::ZERO), &U256::from(2u8));
        assert_eq!(is_some, 1);
        assert_eq!(r, U256::ZERO);
        let (r, is_some) = U256::ct_reduce_wide((U256::from(10u8), U256::ZERO), &U256::from(3u8));
        assert_eq!(is_some, 1);
        assert_eq!(r, U256::ONE);
        let (r, is_some) = U256::ct_reduce_wide((U256::from(10u8), U256::ZERO), &U256::from(7u8));
        assert_eq!(is_some, 1);
        assert_eq!(r, U256::from(3u8));
    }

    #[test]
    fn reduce_max() {
        let mut a = U256::ZERO;
        let mut b = U256::ZERO;
        b.limbs[b.limbs.len() - 1] = Limb(Word::MAX);
        let r = a.wrapping_rem(&b);
        assert_eq!(r, Uint::ZERO);
        a.limbs[a.limbs.len() - 1] = Limb(1 << (HI_BIT - 7));
        b.limbs[b.limbs.len() - 1] = Limb(0x82 << (HI_BIT - 7));
        let r = a.wrapping_rem(&b);
        assert_eq!(r, a);
    }

    #[cfg(feature = "rand")]
    #[test]
    fn reduce2krand() {
        let mut rng = ChaChaRng::from_seed([7u8; 32]);
        for _ in 0..25 {
            let num = U256::random(&mut rng);
            let k = (rng.next_u32() % 256) as usize;
            let den = U256::ONE.shl_vartime(k);

            let a = num.reduce2k(k);
            let e = num.wrapping_rem(&den);
            assert_eq!(a, e);
        }
    }
}
