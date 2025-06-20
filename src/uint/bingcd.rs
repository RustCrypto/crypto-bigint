//! This module implements Binary GCD for [`Uint`]

use crate::const_choice::u32_const_min;
use crate::{NonZero, NonZeroUint, Odd, OddUint, Uint};

impl<const LIMBS: usize> Uint<LIMBS> {
    /// Compute the greatest common divisor of `self` and `rhs`.
    pub const fn bingcd(&self, rhs: &Self) -> Self {
        let self_is_zero = self.is_nonzero().not();
        // Note: is non-zero by construction
        let self_nz = NonZero(Uint::select(self, &Uint::ONE, self_is_zero));
        Uint::select(self_nz.bingcd(rhs).as_ref(), rhs, self_is_zero)
    }

    /// Compute the greatest common divisor of `self` and `rhs`.
    ///
    /// Executes in variable time w.r.t. all input parameters.
    pub const fn bingcd_vartime(&self, rhs: &Self) -> Self {
        let self_is_zero = self.is_nonzero().not();
        // Note: is non-zero by construction
        let self_nz = NonZero(Uint::select(self, &Uint::ONE, self_is_zero));
        Uint::select(self_nz.bingcd(rhs).as_ref(), rhs, self_is_zero)
    }
}

impl<const LIMBS: usize> NonZeroUint<LIMBS> {
    /// Compute the greatest common divisor of `self` and `rhs`.
    pub const fn bingcd(&self, rhs: &Uint<LIMBS>) -> Self {
        let lhs = self.as_ref();

        // Note the following two GCD identity rules:
        // 1) gcd(2a, 2b) = 2 · gcd(a, b), and
        // 2) gcd(a, 2b) = gcd(a, b) if a is odd.
        //
        // Combined, these rules imply that
        // 3) gcd(2^i · a, 2^j · b) = 2^k · gcd(a, b), with k = min(i, j).
        //
        // However, to save ourselves having to divide out 2^j, we also note that
        // 4) 2^k · gcd(a, b) = 2^k · gcd(a, 2^j · b)

        let i = lhs.trailing_zeros();
        let j = rhs.trailing_zeros();
        let k = u32_const_min(i, j);

        let odd_lhs = Odd(lhs.shr(i));
        let gcd_div_2k = odd_lhs.bingcd(rhs);
        NonZero(gcd_div_2k.as_ref().shl(k))
    }

    /// Compute the greatest common divisor of `self` and `rhs`.
    ///
    /// Executes in variable time w.r.t. all input parameters.
    pub const fn bingcd_vartime(&self, rhs: &Uint<LIMBS>) -> Self {
        let lhs = self.as_ref();

        let i = lhs.trailing_zeros_vartime();
        let j = rhs.trailing_zeros_vartime();
        let k = u32_const_min(i, j);

        let odd_lhs = Odd(lhs.shr_vartime(i));
        let gcd_div_2k = odd_lhs.bingcd(rhs);
        NonZero(gcd_div_2k.as_ref().shl_vartime(k))
    }
}

impl<const LIMBS: usize> OddUint<LIMBS> {
    /// Compute the greatest common divisor of `self` and `rhs` using the Binary GCD algorithm.
    ///
    /// This function switches between the "classic" and "optimized" algorithm at a best-effort
    /// threshold. When using [Uint]s with `LIMBS` close to the threshold, it may be useful to
    /// manually test whether the classic or optimized algorithm is faster for your machine.
    #[inline(always)]
    pub const fn bingcd(&self, rhs: &Uint<LIMBS>) -> Self {
        // Todo: tweak this threshold
        if LIMBS < 8 {
            self.classic_bingcd(rhs)
        } else {
            self.optimized_bingcd(rhs)
        }
    }
    /// Compute the greatest common divisor of `self` and `rhs`.
    ///
    /// Executes in variable time w.r.t. all input parameters.
    ///
    /// This function switches between the "classic" and "optimized" algorithm at a best-effort
    /// threshold. When using [Uint]s with `LIMBS` close to the threshold, it may be useful to
    /// manually test whether the classic or optimized algorithm is faster for your machine.
    #[inline(always)]
    pub const fn bingcd_vartime(&self, rhs: &Uint<LIMBS>) -> Self {
        // Todo: tweak this threshold
        if LIMBS < 8 {
            self.classic_bingcd_vartime(rhs)
        } else {
            self.optimized_bingcd_vartime(rhs)
        }
    }
}

#[cfg(feature = "rand_core")]
#[cfg(test)]
mod tests {

    use crate::{U64, U128, U256, U512, U1024, U2048, U4096, Uint};

    fn bingcd_test<const LIMBS: usize>(lhs: Uint<LIMBS>, rhs: Uint<LIMBS>, target: Uint<LIMBS>) {
        assert_eq!(lhs.bingcd(&rhs), target)
    }

    fn bingcd_tests<const LIMBS: usize>() {
        bingcd_test(Uint::<LIMBS>::ZERO, Uint::ZERO, Uint::ZERO);
        bingcd_test(Uint::<LIMBS>::ZERO, Uint::ONE, Uint::ONE);
        bingcd_test(Uint::<LIMBS>::ZERO, Uint::MAX, Uint::MAX);
        bingcd_test(Uint::<LIMBS>::ONE, Uint::ZERO, Uint::ONE);
        bingcd_test(Uint::<LIMBS>::ONE, Uint::ONE, Uint::ONE);
        bingcd_test(Uint::<LIMBS>::ONE, Uint::MAX, Uint::ONE);
        bingcd_test(Uint::<LIMBS>::MAX, Uint::ZERO, Uint::MAX);
        bingcd_test(Uint::<LIMBS>::MAX, Uint::ONE, Uint::ONE);
        bingcd_test(Uint::<LIMBS>::MAX, Uint::MAX, Uint::MAX);
    }

    #[test]
    fn test_bingcd() {
        bingcd_tests::<{ U64::LIMBS }>();
        bingcd_tests::<{ U128::LIMBS }>();
        bingcd_tests::<{ U256::LIMBS }>();
        bingcd_tests::<{ U512::LIMBS }>();
        bingcd_tests::<{ U1024::LIMBS }>();
        bingcd_tests::<{ U2048::LIMBS }>();
        bingcd_tests::<{ U4096::LIMBS }>();
    }
}
