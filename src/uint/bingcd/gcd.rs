use crate::uint::bingcd::tools::{const_max, const_min};
use crate::{NonZero, Odd, Uint, U128, U64};

impl<const LIMBS: usize> NonZero<Uint<LIMBS>> {
    /// Compute the greatest common divisor of `self` and `rhs`.
    pub const fn bingcd(&self, rhs: &Uint<LIMBS>) -> Uint<LIMBS> {
        let val = self.as_ref();
        // Leverage two GCD identity rules to make self and rhs odd.
        // 1) gcd(2a, 2b) = 2 * gcd(a, b)
        // 2) gcd(a, 2b) = gcd(a, b) if a is odd.
        let i = val.is_nonzero().select_u32(0, val.trailing_zeros());
        let j = rhs.is_nonzero().select_u32(0, rhs.trailing_zeros());
        let k = const_min(i, j);

        self.as_ref()
            .shr(i)
            .to_odd()
            .expect("self is odd by construction")
            .bingcd(rhs)
            .shl(k)
    }
}

impl<const LIMBS: usize> Odd<Uint<LIMBS>> {
    const BITS: u32 = Uint::<LIMBS>::BITS;

    /// Compute the greatest common divisor of `self` and `rhs`.
    #[inline(always)]
    pub const fn bingcd(&self, rhs: &Uint<LIMBS>) -> Uint<LIMBS> {
        // Todo: tweak this threshold
        if LIMBS < 8 {
            self.bingcd_small(rhs)
        } else {
            self.bingcd_large::<{ U64::BITS - 2 }, { U64::LIMBS }, { U128::LIMBS }>(rhs)
        }
    }

    /// Computes `gcd(self, rhs)`, leveraging the Binary GCD algorithm.
    /// Is efficient only for relatively small `LIMBS`.
    #[inline]
    pub const fn bingcd_small(&self, rhs: &Uint<LIMBS>) -> Uint<LIMBS> {
        let (mut a, mut b) = (*rhs, *self.as_ref());
        let mut j = 0;
        while j < (2 * Self::BITS - 1) {
            j += 1;

            let a_odd = a.is_odd();

            // swap if a odd and a < b
            let a_lt_b = Uint::lt(&a, &b);
            let do_swap = a_odd.and(a_lt_b);
            Uint::conditional_swap(&mut a, &mut b, do_swap);

            // subtract b from a when a is odd
            a = Uint::select(&a, &a.wrapping_sub(&b), a_odd);

            // Div a by two when b ≠ 0, otherwise do nothing.
            let do_apply = b.is_nonzero();
            a = Uint::select(&a, &a.shr_vartime(1), do_apply);
        }

        b
    }

    /// Computes `gcd(self, rhs)`, leveraging the Binary GCD algorithm.
    /// Is efficient for larger `LIMBS`.
    #[inline(always)]
    pub const fn bingcd_large<const K: u32, const LIMBS_K: usize, const LIMBS_2K: usize>(
        &self,
        rhs: &Uint<LIMBS>,
    ) -> Uint<LIMBS> {
        let (mut a, mut b) = (*rhs, *self.as_ref());

        let mut i = 0;
        while i < (2 * Self::BITS - 1).div_ceil(K) {
            i += 1;

            // Construct a_ and b_ as the summary of a and b, respectively.
            let n = const_max(2 * K, const_max(a.bits(), b.bits()));
            let a_ = a.compact::<LIMBS_2K>(n, K);
            let b_ = b.compact::<LIMBS_2K>(n, K);

            // Compute the K-1 iteration update matrix from a_ and b_
            let (matrix, log_upper_bound) = Uint::restricted_extended_gcd::<LIMBS_K>(a_, b_, K - 1);

            // Update `a` and `b` using the update matrix
            let (updated_a, updated_b) = matrix.extended_apply_to((a, b));

            a = updated_a
                .div_2k(log_upper_bound)
                .abs_drop_extension()
                .expect("extension is zero");
            b = updated_b
                .div_2k(log_upper_bound)
                .abs_drop_extension()
                .expect("extension is zero");
        }

        b
    }
}

#[cfg(feature = "rand_core")]
#[cfg(test)]
mod tests {
    use crate::{Gcd, Random, Uint, U256, U512};
    use rand_core::OsRng;

    fn test_bingcd_small<const LIMBS: usize>()
    where
        Uint<LIMBS>: Gcd<Output = Uint<LIMBS>>,
    {
        for _ in 0..100 {
            let x = Uint::<LIMBS>::random(&mut OsRng);
            let mut y = Uint::<LIMBS>::random(&mut OsRng);

            y = Uint::select(&(y.wrapping_add(&Uint::ONE)), &y, y.is_odd());

            let gcd = x.gcd(&y);
            let bingcd = y.to_odd().unwrap().bingcd(&x);
            assert_eq!(gcd, bingcd);
        }
    }

    #[test]
    fn testing_bingcd_small() {
        test_bingcd_small::<{ U256::LIMBS }>();
        test_bingcd_small::<{ U512::LIMBS }>();
    }
}
