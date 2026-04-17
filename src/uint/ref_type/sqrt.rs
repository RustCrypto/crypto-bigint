//! Square root calculation.

use super::UintRef;
use crate::{Choice, Limb, NonZero, Uint, WideWord, Word, word};

impl UintRef {
    #[inline]
    pub(crate) const fn sqrt_assign(&mut self, buf: (&mut UintRef, &mut UintRef)) -> Choice {
        assert!(buf.0.nlimbs() >= self.nlimbs() && buf.1.nlimbs() >= self.nlimbs());

        if self.nlimbs() == 0 {
            return Choice::TRUE;
        }

        let mut bits = self.bits();
        let is_zero = Choice::from_u32_nz(bits).not();
        // Set first limb to 1 if the input is zero
        self.limbs[0] = Limb::select(self.limbs[0], Limb::ONE, is_zero);
        bits = is_zero.select_u32(bits, 1);

        // Shift such that at least one of the top two bits are non-zero
        let s_shift = (self.bits_precision() - bits) >> 1;
        self.shl_assign(s_shift * 2);

        // Compute root and uncorrected remainder, placing them in buf.0 and buf.1
        self.sqrt_rem_normalized(buf.0, buf.1);

        // Copy the shifted root to self and correct it
        self.copy_from(buf.0.leading(self.nlimbs()));
        self.shr_assign(s_shift);

        // Set root to zero if self was zero
        self.limbs[0] = Limb::select(self.limbs[0], Limb::ZERO, is_zero);

        // Check if there is a remainder
        buf.1.is_zero()
    }

    #[inline]
    pub(crate) const fn sqrt_assign_vartime(&mut self, buf: (&mut UintRef, &mut UintRef)) -> bool {
        let bits = self.bits_vartime();
        if bits == 0 {
            return true;
        }

        let words = bits.div_ceil(Limb::BITS);
        let lz = words * Limb::BITS - bits;
        assert!(buf.0.nlimbs() >= words as usize && buf.1.nlimbs() >= words as usize);

        // Shift such that at least one of the top two bits are non-zero
        let s_shift = lz >> 1;
        self.shl_assign_limb_vartime(s_shift * 2);

        // Only consider the populated limbs
        let out = self.leading_mut(words as usize);

        // Compute root and uncorrected remainder, placing them in buf.0 and buf.1
        out.sqrt_rem_normalized(buf.0, buf.1);

        // Copy the shifted root to self and correct it
        out.copy_from(buf.0.leading(out.nlimbs()));
        out.shr_assign_limb_vartime(s_shift);

        // Check if there is a remainder
        buf.1.is_zero_vartime()
    }

    /// Uses Brent & Zimmermann, Modern Computer Arithmetic, v0.5.9, Algorithm 1.12
    #[allow(clippy::cast_possible_truncation)]
    const fn sqrt_rem_normalized(&self, s: &mut UintRef, r: &mut UintRef) {
        let len = self.nlimbs();

        // Handle base case of a square root <= 3 limbs
        if len < 4 {
            if len == 0 {
                // no input
                return;
            }

            // Compute root, remainder for a single word
            let (s1, r1) = sqrt_rem_word(self.limbs[len - 1].0);
            if len == 1 {
                (s.limbs[0].0, r.limbs[0].0) = (s1, r1);
                return;
            }

            // Expand to root, remainder for two words
            let (s1, r1) = sqrt_rem_expand(s1, r1 as WideWord, self.limbs[len - 2].0);
            if len == 2 {
                s.limbs[0].0 = s1 as Word;
                (r.limbs[0].0, r.limbs[1].0) = word::split_wide(r1);
                return;
            }

            // Expand to root, remainder for three words
            let (s1, r1) = sqrt_rem_expand(s1 as Word, r1, self.limbs[len - 3].0);
            (s.limbs[0].0, s.limbs[1].0) = word::split_wide(s1);
            (r.limbs[0].0, r.limbs[1].0) = word::split_wide(r1);
            return;
        }

        let l = len >> 2;
        let rt_len = (len - l * 2).div_ceil(2);
        let (a_lo, a_hi) = self.split_at(l * 2);
        let (a0, a1) = a_lo.split_at(l);

        // Compute (s', r') <- SqrtRem(a3ß + a2), storing s' and r' in the high (+l) limbs of s, r
        a_hi.sqrt_rem_normalized(s.trailing_mut(l), r.trailing_mut(l));

        let (s0, s1) = s.split_at_mut(l);
        let (s1, s2) = s1.split_at_mut(rt_len);

        // Set u = s' and shift to the top
        let u = s2.leading_mut(rt_len + 1);
        u.leading_mut(rt_len).copy_from(s1);
        u.limbs[rt_len] = Limb::ZERO;
        let ulz = u.leading_zeros();
        u.shl_assign(ulz);
        let uwords = u.nlimbs() as u32 - ((ulz - 1) >> Limb::LOG2_BITS);

        // Set q = r'B + a1 and shift to match u
        let q = r.leading_mut(l + rt_len + 1);
        q.leading_mut(l).copy_from(a1);
        let lshift = (ulz - 1) & (Limb::BITS - 1);
        let q_hi = q.shl_assign_limb(lshift);

        // Divide q/u, setting q to the quotient and u to the remainder
        q.div_rem_shifted(q_hi, u, uwords);
        q.unbounded_shr_assign_by_limbs(uwords - 1);
        u.shr_assign_limb(lshift);

        s0.copy_from(q.leading(l));
        let q_hi = q.limbs[l];
        s1.add_assign_limb(q_hi);
        debug_assert!(q_hi.0 & !1 == 0);

        let (r, r_tail) = r.split_at_mut(l + rt_len + 1);
        let (r_lo, r_hi) = r.split_at_mut(l);
        r_lo.copy_from(a0);
        r_hi.copy_from(u);

        // Compute q^2
        let q2 = s2.leading_mut(l * 2);
        q2.fill(Limb::ZERO);
        s0.wrapping_square(q2);

        // Subtract q^2 from r, producing a borrow if r < 0
        let (r0, r1) = r.split_at_mut(l * 2);
        let borrow = r0.borrowing_sub_assign(q2, Limb::ZERO);
        let swap = r1.borrowing_sub_assign_limb(q_hi, borrow).lsb_to_choice();

        // s -= 1 if r < 0
        let (s, s_tail) = s.split_at_mut(l + rt_len);
        s.borrowing_sub_assign_limb(Limb::select(Limb::ZERO, Limb::ONE, swap), Limb::ZERO);

        // r += 2s + 1 if r < 0
        let s_mul = Limb::select(Limb::ZERO, Limb(2), swap);
        let s_carry = s_mul.shr(1);
        r.carrying_add_assign_mul_limb(s, s_mul, s_carry);

        s_tail.fill(Limb::ZERO);
        r_tail.fill(Limb::ZERO);
    }
}

/// Compute the square root and remainder of a [`Word`].
///
/// Adapted from Hacker's Delight 2E by Henry S. Warren Jr.,
/// Fig. 11-4, "Integer square root, hardware algorithm"
/// based on Toepler's algorithm.
#[inline]
const fn sqrt_rem_word(value: Word) -> (Word, Word) {
    let mut m = 1 << (Word::BITS - 2);
    let mut x = value;
    let mut y = 0;
    while m != 0 {
        let b = y | m;
        y >>= 1;
        let cmp = word::choice_from_le(b, x);
        x = word::select(x, x.wrapping_sub(b), cmp);
        y = word::select(y, y | m, cmp);
        m >>= 2;
    }
    (y, x)
}

/// Compute the square root and remainder of a [`WideWord`].
///
/// `value` must be non-zero and normalized such that at least one of the top
/// two bits is set.
#[inline]
#[allow(clippy::cast_possible_truncation)]
const fn sqrt_rem_expand(s1: Word, r1: WideWord, next: Word) -> (WideWord, WideWord) {
    const HALF_WIDTH: u32 = Word::BITS >> 1;

    let (a0, a1) = (
        (next & ((1 << HALF_WIDTH) - 1)) as WideWord,
        (next >> HALF_WIDTH) as WideWord,
    );
    let d = (r1 << HALF_WIDTH) | a1;
    let (q, _) = Uint::<2>::from_wide_word(d).div_rem_limb(NonZero::<Limb>::new_unwrap(Limb(s1)));
    let q = q.limbs[0].0 as WideWord >> 1;
    let u = Limb((d - 2 * q * s1 as WideWord) as _);
    let s = ((s1 as WideWord) << HALF_WIDTH) + q;
    let q2 = q.pow(2);
    let r_pre = ((u.0 as WideWord) << HALF_WIDTH) | a0;
    let swap = word::choice_from_wide_lt(r_pre, q2);
    let s = word::select_wide(s, s - 1, swap);
    let r = word::select_wide(r_pre, r_pre.wrapping_add(2 * s + 1), swap) - q2;
    (s, r)
}

#[cfg(test)]
mod tests {
    use super::{sqrt_rem_expand, sqrt_rem_word};
    use crate::{WideWord, Word};

    #[test]
    fn sqrt_rem_word_expected() {
        fn check(val: Word) {
            let (root, rem) = sqrt_rem_word(val);
            let check = root.pow(2) + rem;
            assert_eq!(check, val, "val: {val}, root: {root}, rem: {rem}");
        }

        check(0);
        check(1);
        check(2);
        check(Word::MAX);
    }

    #[test]
    fn sqrt_expand_expected() {
        fn check(s1: Word, r1: WideWord, next: Word, s2: WideWord, r2: WideWord) {
            let (s_res, r_res) = sqrt_rem_expand(s1, r1, next);
            assert_eq!(s2, s_res);
            assert_eq!(r2, r_res);
        }

        check(
            622260355,
            205765663,
            1685072410847819194,
            2672587875032468269,
            3184677644130930641,
        );
        check(
            2672587875032468269,
            3184677644130930641,
            15850601984282720829,
            0x2516f0832a538b2d98869e21,
            0x4a2de10654a7165b310d39fc,
        );
    }
}
