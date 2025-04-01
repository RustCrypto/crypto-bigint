use crate::{ConstChoice, Limb, Odd, Uint};

/// `const` equivalent of `u32::max(a, b)`.
pub(crate) const fn const_max(a: u32, b: u32) -> u32 {
    ConstChoice::from_u32_lt(a, b).select_u32(a, b)
}

/// `const` equivalent of `u32::min(a, b)`.
pub(crate) const fn const_min(a: u32, b: u32) -> u32 {
    ConstChoice::from_u32_lt(a, b).select_u32(b, a)
}

impl Limb {
    /// Compute `self / 2^k mod q`. Returns the result, as well as a factor `f` such that `2^k`
    /// divides `self + q * f`.
    ///
    /// Executes in time variable in `k_bound`. This value should be chosen as an inclusive
    /// upperbound to the value of `k`.
    const fn bounded_div2k_mod_q(
        mut self,
        k: u32,
        k_bound: u32,
        one_half_mod_q: Self,
    ) -> (Self, Self) {
        let mut factor = Limb::ZERO;
        let mut i = 0;
        while i < k_bound {
            let execute = ConstChoice::from_u32_lt(i, k);

            let (shifted, carry) = self.shr1();
            self = Self::select(self, shifted, execute);

            let overflow = ConstChoice::from_word_msb(carry.0);
            let add_back_q = overflow.and(execute);
            self = self.wrapping_add(Self::select(Self::ZERO, one_half_mod_q, add_back_q));
            factor = factor.bitxor(Self::select(Self::ZERO, Self::ONE.shl(i), add_back_q));
            i += 1;
        }

        (self, factor)
    }
}

impl<const LIMBS: usize> Uint<LIMBS> {
    /// Compute `self / 2^k  mod q`.
    ///
    /// Executes in time variable in `k_bound`. This value should be
    /// chosen as an inclusive upperbound to the value of `k`.
    #[inline]
    pub(crate) const fn div_2k_mod_q(mut self, k: u32, k_bound: u32, q: &Odd<Self>) -> Self {
        //        1  / 2      mod q
        // = (q + 1) / 2      mod q
        // = (q - 1) / 2  + 1 mod q
        // = floor(q / 2) + 1 mod q, since q is odd.
        let one_half_mod_q = q.as_ref().shr_vartime(1).wrapping_add(&Uint::ONE);
        let mut i = 0;
        while i < k_bound {
            // Apply only while i < k
            let apply = ConstChoice::from_u32_lt(i, k);
            self = Self::select(&self, &self.div_2_mod_q(&one_half_mod_q), apply);
            i += 1;
        }

        self
    }

    /// Computes `self + (b * c) + carry`, returning the result along with the new carry.
    #[inline]
    const fn mac_limb(mut self, b: &Self, c: Limb, mut carry: Limb) -> (Self, Limb) {
        let mut i = 0;
        while i < LIMBS {
            (self.limbs[i], carry) = self.limbs[i].mac(b.limbs[i], c, carry);
            i += 1;
        }
        (self, carry)
    }

    /// Compute `self / 2 mod q`.
    #[inline]
    const fn div_2_mod_q(self, half_mod_q: &Self) -> Self {
        // Floor-divide self by 2. When self was odd, add back 1/2 mod q.
        let (floored_half, add_one_half) = self.shr1_with_carry();
        floored_half.wrapping_add(&Self::select(&Self::ZERO, half_mod_q, add_one_half))
    }

    /// Construct a [Uint] containing the bits in `self` in the range `[idx, idx + length)`.
    ///
    /// Assumes `length ≤ Uint::<SECTION_LIMBS>::BITS` and `idx + length ≤ Self::BITS`.
    ///
    /// Executes in time variable in `length` only.
    #[inline(always)]
    pub(crate) const fn section_vartime_length<const SECTION_LIMBS: usize>(
        &self,
        idx: u32,
        length: u32,
    ) -> Uint<SECTION_LIMBS> {
        debug_assert!(length <= Uint::<SECTION_LIMBS>::BITS);
        debug_assert!(idx + length <= Self::BITS);

        let mask = Uint::ONE.shl_vartime(length).wrapping_sub(&Uint::ONE);
        self.shr(idx).resize::<SECTION_LIMBS>().bitand(&mask)
    }

    /// Construct a [Uint] containing the bits in `self` in the range `[idx, idx + length)`.
    ///
    /// Assumes `length ≤ Uint::<SECTION_LIMBS>::BITS` and `idx + length ≤ Self::BITS`.
    ///
    /// Executes in time variable in `idx` and `length`.
    #[inline(always)]
    pub(crate) const fn section_vartime<const SECTION_LIMBS: usize>(
        &self,
        idx: u32,
        length: u32,
    ) -> Uint<SECTION_LIMBS> {
        debug_assert!(length <= Uint::<SECTION_LIMBS>::BITS);
        debug_assert!(idx + length <= Self::BITS);

        let mask = Uint::ONE.shl_vartime(length).wrapping_sub(&Uint::ONE);
        self.shr_vartime(idx)
            .resize::<SECTION_LIMBS>()
            .bitand(&mask)
    }

    /// Compact `self` to a form containing the concatenation of its bit ranges `[0, K-1)`
    /// and `[n-K-1, n)`.
    ///
    /// Assumes `K ≤ Uint::<SUMMARY_LIMBS>::BITS`, `n ≤ Self::BITS` and `n ≥ 2K`.
    #[inline(always)]
    pub(crate) const fn compact<const K: u32, const SUMMARY_LIMBS: usize>(
        &self,
        n: u32,
    ) -> Uint<SUMMARY_LIMBS> {
        debug_assert!(K <= Uint::<SUMMARY_LIMBS>::BITS);
        debug_assert!(n <= Self::BITS);
        debug_assert!(n >= 2 * K);

        // safe to vartime; this function is vartime in length only, which is a public constant
        let hi = self.section_vartime_length(n - K - 1, K + 1);
        // safe to vartime; this function is vartime in idx and length only, which are both public
        // constants
        let lo = self.section_vartime(0, K - 1);
        // safe to vartime; shl_vartime is variable in the value of shift only. Since this shift
        // is a public constant, the constant time property of this algorithm is not impacted.
        hi.shl_vartime(K - 1).bitxor(&lo)
    }
}

#[cfg(test)]
mod tests {
    use crate::{Limb, U128, Uint};

    #[test]
    fn test_bounded_div2k_mod_q() {
        let x = Limb::MAX.wrapping_sub(Limb::from(15u32));
        let q = Limb::from(55u32);
        let half_mod_q = q.shr1().0.wrapping_add(Limb::ONE);

        // Do nothing
        let k = 0;
        let k_bound = 3;
        let (res, factor) = x.bounded_div2k_mod_q(k, k_bound, half_mod_q);
        assert_eq!(res, x);
        assert_eq!(factor, Limb::ZERO);

        // Divide by 2^4 without requiring the addition of q
        let k = 4;
        let k_bound = 4;
        let (res, factor) = x.bounded_div2k_mod_q(k, k_bound, half_mod_q);
        assert_eq!(res, x.shr(4));
        assert_eq!(factor, Limb::ZERO);

        // Divide by 2^5, requiring a single addition of q * 2^4
        let k = 5;
        let k_bound = 5;
        let (res, factor) = x.bounded_div2k_mod_q(k, k_bound, half_mod_q);
        assert_eq!(res, x.shr(5).wrapping_add(half_mod_q));
        assert_eq!(factor, Limb::ONE.shl(4));

        // Execute at most k_bound iterations
        let k = 5;
        let k_bound = 4;
        let (res, factor) = x.bounded_div2k_mod_q(k, k_bound, half_mod_q);
        assert_eq!(res, x.shr(4));
        assert_eq!(factor, Limb::ZERO);
    }

    #[test]
    fn test_mac_limb() {
        // Do nothing
        let x = U128::from_be_hex("ABCDEF98765432100123456789FEDCBA");
        let q = U128::MAX;
        let f = Limb::ZERO;
        let (res, carry) = x.mac_limb(&q, f, Limb::ZERO);
        assert_eq!(res, x);
        assert_eq!(carry, Limb::ZERO);

        // f = 1
        let x = U128::from_be_hex("ABCDEF98765432100123456789FEDCBA");
        let q = U128::MAX;
        let f = Limb::ONE;
        let (res, carry) = x.mac_limb(&q, f, Limb::ZERO);
        assert_eq!(res, x.wrapping_add(&q));
        assert_eq!(carry, Limb::ONE);

        // f = max
        let x = U128::from_be_hex("ABCDEF98765432100123456789FEDCBA");
        let q = U128::MAX;
        let f = Limb::MAX;
        let (res, mac_carry) = x.mac_limb(&q, f, Limb::ZERO);
        let (qf_lo, qf_hi) = q.split_mul(&Uint::new([f; 1]));
        let (lo, carry) = qf_lo.adc(&x, Limb::ZERO);
        let (hi, carry) = qf_hi.adc(&Uint::ZERO, carry);
        assert_eq!(res, lo);
        assert_eq!(mac_carry, hi.limbs[0]);
        assert_eq!(carry, Limb::ZERO)
    }
}
