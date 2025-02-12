//! This module implements (a constant variant of) the Optimized Extended Binary GCD algorithm,
//! which is described by Pornin in "Optimized Binary GCD for Modular Inversion".
//! Ref: <https://eprint.iacr.org/2020/972.pdf>

use crate::uint::bingcd::tools::const_min;
use crate::{ConcatMixed, ConstChoice, Int, NonZero, Odd, Uint};

impl<const LIMBS: usize> Int<LIMBS> {
    /// Compute the gcd of `self` and `rhs` leveraging the Binary GCD algorithm.
    pub const fn bingcd(&self, rhs: &Self) -> Uint<LIMBS> {
        self.abs().bingcd(&rhs.abs())
    }

    /// Executes the Binary Extended GCD algorithm.
    ///
    /// Given `(self, rhs)`, computes `(g, x, y)`, s.t. `self * x + rhs * y = g = gcd(self, rhs)`.
    pub fn binxgcd<const DOUBLE: usize>(&self, rhs: &Self) -> (Uint<LIMBS>, Self, Self)
    where
        Uint<LIMBS>: ConcatMixed<Uint<LIMBS>, MixedOutput=Uint<DOUBLE>>
    {
        // Make sure `self` and `rhs` are nonzero.
        let self_is_zero = self.is_nonzero().not();
        let self_nz = Int::select(self, &Int::ONE, self_is_zero)
            .to_nz()
            .expect("self is non zero by construction");
        let rhs_is_zero = rhs.is_nonzero().not();
        let rhs_nz = Int::select(rhs, &Int::ONE, rhs_is_zero)
            .to_nz()
            .expect("self is non zero by construction");

        let (gcd, mut x, mut y) = self_nz.binxgcd(&rhs_nz);

        // Account for the case that self or rhs was zero
        let gcd = Uint::select(gcd.as_ref(), &rhs.abs(), self_is_zero);
        let gcd = Uint::select(&gcd, &self.abs(), rhs_is_zero);
        x = Int::select(&x, &Int::ZERO, self_is_zero);
        y = Int::select(&y, &Int::ONE, self_is_zero);
        x = Int::select(&x, &Int::ONE, rhs_is_zero);
        y = Int::select(&y, &Int::ZERO, rhs_is_zero);

        (gcd, x, y)
    }
}

impl<const LIMBS: usize> NonZero<Int<LIMBS>> {
    /// Execute the Binary Extended GCD algorithm.
    ///
    /// Given `(self, rhs)`, computes `(g, x, y)` s.t. `self * x + rhs * y = g = gcd(self, rhs)`.
    pub fn binxgcd<const DOUBLE: usize>(&self, rhs: &Self) -> (NonZero<Uint<LIMBS>>, Int<LIMBS>, Int<LIMBS>)
    where
        Uint<LIMBS>: ConcatMixed<Uint<LIMBS>, MixedOutput=Uint<DOUBLE>>
    {
        let (mut lhs, mut rhs) = (*self.as_ref(), *rhs.as_ref());
        // Leverage two GCD identity rules to make self and rhs odd.
        // 1) gcd(2a, 2b) = 2 * gcd(a, b)
        // 2) gcd(a, 2b) = gcd(a, b) if a is odd.
        let i = lhs.is_nonzero().select_u32(0, lhs.0.trailing_zeros());
        let j = rhs.is_nonzero().select_u32(0, rhs.0.trailing_zeros());
        let k = const_min(i, j);

        // Remove the common factor `2^k` from both lhs and rhs.
        lhs = lhs.shr(k);
        rhs = rhs.shr(k);
        // At this point, either lhs or rhs is odd (or both).
        // Switch them to make sure lhs is odd.
        let do_swap = ConstChoice::from_u32_lt(j, i);
        Int::conditional_swap(&mut lhs, &mut rhs, do_swap);
        let lhs_ = lhs.to_odd().expect("lhs is odd by construction");

        // Compute the xgcd for odd lhs_ and rhs_
        let rhs_nz = rhs.to_nz().expect("rhs is non-zero by construction");
        let (gcd, mut x, mut y) = lhs_.binxgcd(&rhs_nz);

        // Account for the fact that we may have previously swapped lhs and rhs.
        Int::conditional_swap(&mut x, &mut y, do_swap);
        (
            gcd.as_ref()
                .shl(k)
                .to_nz()
                .expect("gcd of non-zero element with another element is non-zero"),
            x,
            y,
        )
    }
}

impl<const LIMBS: usize> Odd<Int<LIMBS>> {
    /// Execute the Binary Extended GCD algorithm.
    ///
    /// Given `(self, rhs)`, computes `(g, x, y)` s.t. `self * x + rhs * y = g = gcd(self, rhs)`.
    pub fn binxgcd<const DOUBLE: usize>(
        &self,
        rhs: &NonZero<Int<LIMBS>>,
    ) -> (Odd<Uint<LIMBS>>, Int<LIMBS>, Int<LIMBS>)
    where
        Uint<LIMBS>: ConcatMixed<Uint<LIMBS>, MixedOutput=Uint<DOUBLE>>
    {
        let (abs_lhs, sgn_lhs) = self.abs_sign();
        let (abs_rhs, sgn_rhs) = rhs.abs_sign();

        // Make rhs odd
        let rhs_is_odd = ConstChoice::from_u32_eq(abs_rhs.as_ref().trailing_zeros(), 0);
        let rhs_gt_lhs = Uint::gt(&abs_rhs.as_ref(), abs_lhs.as_ref());
        let abs_rhs = Uint::select(
            &Uint::select(
                &abs_lhs.as_ref().wrapping_sub(&abs_rhs.as_ref()),
                &abs_rhs.as_ref().wrapping_sub(&abs_lhs.as_ref()),
                rhs_gt_lhs,
            ),
            &abs_rhs.as_ref(),
            rhs_is_odd,
        );
        let rhs_ = abs_rhs.to_odd().expect("rhs is odd by construction");

        let (gcd, mut x, mut y) = abs_lhs.limited_binxgcd(&rhs_);

        let x_lhs = x.widening_mul_uint(abs_lhs.as_ref());
        let y_rhs = y.widening_mul_uint(&abs_rhs);
        debug_assert_eq!(x_lhs.wrapping_add(&y_rhs), gcd.resize().as_int());

        // At this point, we have one of the following three situations:
        // i.   gcd = lhs * x + (rhs - lhs) * y, if rhs is even and rhs > lhs
        // ii.  gcd = lhs * x + (lhs - rhs) * y, if rhs is even and rhs < lhs
        // iii. gcd = lhs * x + rhs * y, if rhs is odd

        // Reverse-engineering the bezout coefficients for lhs and rhs, we get
        // i.   gcd = lhs * (x - y) + rhs * y, if rhs is even and rhs > lhs
        // ii.  gcd = lhs * (x + y) - y * rhs, if rhs is even and rhs < lhs
        // iii. gcd = lhs * x + rhs * y, if rhs is odd

        x = Int::select(&x, &x.wrapping_sub(&y), rhs_is_odd.not().and(rhs_gt_lhs));
        x = Int::select(
            &x,
            &x.wrapping_add(&y),
            rhs_is_odd.not().and(rhs_gt_lhs.not()),
        );
        y = y.wrapping_neg_if(rhs_is_odd.not().and(rhs_gt_lhs.not()));

        let x_lhs = x.widening_mul_uint(abs_lhs.as_ref());
        let y_rhs = y.widening_mul_uint(&rhs.abs());
        debug_assert_eq!(x_lhs.wrapping_add(&y_rhs), gcd.resize().as_int());

        (gcd, x.wrapping_neg_if(sgn_lhs), y.wrapping_neg_if(sgn_rhs))
    }
}

#[cfg(test)]
mod test {

    mod test_int_binxgcd {
        use crate::{
            ConcatMixed, Int, Random, Uint, U1024, U128, U192, U2048, U256, U384, U4096, U512, U64,
            U768, U8192,
        };
        use rand_core::OsRng;

        fn int_binxgcd_test<const LIMBS: usize, const DOUBLE: usize>(
            lhs: Int<LIMBS>,
            rhs: Int<LIMBS>,
        ) where
            Uint<LIMBS>: ConcatMixed<Uint<LIMBS>, MixedOutput = Uint<DOUBLE>>,
        {
            let gcd = lhs.bingcd(&rhs);
            let (xgcd, x, y) = lhs.binxgcd(&rhs);
            assert_eq!(gcd, xgcd);
            assert_eq!(
                x.widening_mul(&lhs).wrapping_add(&y.widening_mul(&rhs)),
                xgcd.resize().as_int()
            );
        }

        fn int_binxgcd_tests<const LIMBS: usize, const DOUBLE: usize>()
        where
            Uint<LIMBS>: ConcatMixed<Uint<LIMBS>, MixedOutput = Uint<DOUBLE>>,
        {
            int_binxgcd_test(Int::MIN, Int::MIN);
            int_binxgcd_test(Int::MIN, Int::MINUS_ONE);
            int_binxgcd_test(Int::MIN, Int::ZERO);
            int_binxgcd_test(Int::MIN, Int::ONE);
            int_binxgcd_test(Int::MIN, Int::MAX);
            int_binxgcd_test(Int::ONE, Int::MIN);
            int_binxgcd_test(Int::ONE, Int::MINUS_ONE);
            int_binxgcd_test(Int::ONE, Int::ZERO);
            int_binxgcd_test(Int::ONE, Int::ONE);
            int_binxgcd_test(Int::ONE, Int::MAX);
            int_binxgcd_test(Int::ZERO, Int::MIN);
            int_binxgcd_test(Int::ZERO, Int::MINUS_ONE);
            int_binxgcd_test(Int::ZERO, Int::ZERO);
            int_binxgcd_test(Int::ZERO, Int::ONE);
            int_binxgcd_test(Int::ZERO, Int::MAX);
            int_binxgcd_test(Int::ONE, Int::MIN);
            int_binxgcd_test(Int::ONE, Int::MINUS_ONE);
            int_binxgcd_test(Int::ONE, Int::ZERO);
            int_binxgcd_test(Int::ONE, Int::ONE);
            int_binxgcd_test(Int::ONE, Int::MAX);
            int_binxgcd_test(Int::MAX, Int::MIN);
            int_binxgcd_test(Int::MAX, Int::MINUS_ONE);
            int_binxgcd_test(Int::MAX, Int::ZERO);
            int_binxgcd_test(Int::MAX, Int::ONE);
            int_binxgcd_test(Int::MAX, Int::MAX);

            for _ in 0..100 {
                let x = Int::random(&mut OsRng);
                let y = Int::random(&mut OsRng);
                int_binxgcd_test(x, y);
            }
        }

        #[test]
        fn test_int_binxgcd() {
            int_binxgcd_tests::<{ U64::LIMBS }, { U128::LIMBS }>();
            int_binxgcd_tests::<{ U128::LIMBS }, { U256::LIMBS }>();
            int_binxgcd_tests::<{ U192::LIMBS }, { U384::LIMBS }>();
            int_binxgcd_tests::<{ U256::LIMBS }, { U512::LIMBS }>();
            int_binxgcd_tests::<{ U384::LIMBS }, { U768::LIMBS }>();
            int_binxgcd_tests::<{ U512::LIMBS }, { U1024::LIMBS }>();
            int_binxgcd_tests::<{ U1024::LIMBS }, { U2048::LIMBS }>();
            int_binxgcd_tests::<{ U2048::LIMBS }, { U4096::LIMBS }>();
            int_binxgcd_tests::<{ U4096::LIMBS }, { U8192::LIMBS }>();
        }
    }

    mod test_nonzero_int_binxgcd {
        use crate::{ConcatMixed, Int, NonZero, Uint, U1024, U128, U192, U2048, U256, U384, U4096, U512, U64, U768, U8192, RandomMod, Gcd};
        use rand_core::OsRng;

        fn nz_int_binxgcd_test<const LIMBS: usize, const DOUBLE: usize>(
            lhs: NonZero<Int<LIMBS>>,
            rhs: NonZero<Int<LIMBS>>,
        ) where
            Uint<LIMBS>: ConcatMixed<Uint<LIMBS>, MixedOutput = Uint<DOUBLE>>,
            Int<LIMBS>: Gcd<Output=Uint<LIMBS>>
        {
            let gcd = lhs.gcd(&rhs);
            let (xgcd, x, y) = lhs.binxgcd(&rhs);
            assert_eq!(gcd.to_nz().unwrap(), xgcd);
            assert_eq!(
                x.widening_mul(&lhs).wrapping_add(&y.widening_mul(&rhs)),
                xgcd.resize().as_int()
            );
        }

        fn nz_int_binxgcd_tests<const LIMBS: usize, const DOUBLE: usize>()
        where
            Uint<LIMBS>: ConcatMixed<Uint<LIMBS>, MixedOutput = Uint<DOUBLE>>,
            Int<LIMBS>: Gcd<Output=Uint<LIMBS>>
        {
            let nz_min = Int::MIN.to_nz().expect("is nz");
            let nz_minus_one = Int::MINUS_ONE.to_nz().expect("is nz");
            let nz_one = Int::ONE.to_nz().expect("is nz");
            let nz_max = Int::MAX.to_nz().expect("is nz");

            nz_int_binxgcd_test(nz_min, nz_min);
            nz_int_binxgcd_test(nz_min, nz_minus_one);
            nz_int_binxgcd_test(nz_min, nz_one);
            nz_int_binxgcd_test(nz_min, nz_max);
            nz_int_binxgcd_test(nz_one, nz_min);
            nz_int_binxgcd_test(nz_one, nz_minus_one);
            nz_int_binxgcd_test(nz_one, nz_one);
            nz_int_binxgcd_test(nz_one, nz_max);
            nz_int_binxgcd_test(nz_max, nz_min);
            nz_int_binxgcd_test(nz_max, nz_minus_one);
            nz_int_binxgcd_test(nz_max, nz_one);
            nz_int_binxgcd_test(nz_max, nz_max);

            let bound = Int::MIN.abs().to_nz().unwrap();
            for _ in 0..100 {
                let x = Uint::random_mod(&mut OsRng, &bound).as_int().to_nz().unwrap();
                let y = Uint::random_mod(&mut OsRng, &bound).as_int().to_nz().unwrap();
                nz_int_binxgcd_test(x, y);
            }
        }

        #[test]
        fn test_nz_int_binxgcd() {
            // nz_int_binxgcd_tests::<{ U64::LIMBS }, { U128::LIMBS }>();
            // nz_int_binxgcd_tests::<{ U128::LIMBS }, { U256::LIMBS }>();
            // nz_int_binxgcd_tests::<{ U192::LIMBS }, { U384::LIMBS }>();
            // nz_int_binxgcd_tests::<{ U256::LIMBS }, { U512::LIMBS }>();
            // nz_int_binxgcd_tests::<{ U384::LIMBS }, { U768::LIMBS }>();
            nz_int_binxgcd_tests::<{ U512::LIMBS }, { U1024::LIMBS }>();
            nz_int_binxgcd_tests::<{ U1024::LIMBS }, { U2048::LIMBS }>();
            nz_int_binxgcd_tests::<{ U2048::LIMBS }, { U4096::LIMBS }>();
            nz_int_binxgcd_tests::<{ U4096::LIMBS }, { U8192::LIMBS }>();
        }
    }

    mod test_odd_int_binxgcd {
        use crate::{
            ConcatMixed, Int, Odd, Random, Uint, U1024, U128, U192, U2048, U256, U384, U4096, U512,
            U64, U768, U8192,
        };
        use rand_core::OsRng;

        fn odd_int_binxgcd_test<const LIMBS: usize, const DOUBLE: usize>(
            lhs: Odd<Int<LIMBS>>,
            rhs: Odd<Int<LIMBS>>,
        ) where
            Uint<LIMBS>: ConcatMixed<Uint<LIMBS>, MixedOutput = Uint<DOUBLE>>,
        {
            let gcd = lhs.bingcd(&rhs);
            let (xgcd, x, y) = lhs.binxgcd(&rhs.as_ref().to_nz().unwrap());
            assert_eq!(gcd.to_odd().unwrap(), xgcd);
            assert_eq!(
                x.widening_mul(&lhs).wrapping_add(&y.widening_mul(&rhs)),
                xgcd.resize().as_int()
            );
        }

        fn odd_int_binxgcd_tests<const LIMBS: usize, const DOUBLE: usize>()
        where
            Uint<LIMBS>: ConcatMixed<Uint<LIMBS>, MixedOutput = Uint<DOUBLE>>,
        {
            let neg_max = Int::MAX.wrapping_neg();
            odd_int_binxgcd_test(neg_max.to_odd().unwrap(), neg_max.to_odd().unwrap());
            odd_int_binxgcd_test(neg_max.to_odd().unwrap(), Int::MINUS_ONE.to_odd().unwrap());
            odd_int_binxgcd_test(neg_max.to_odd().unwrap(), Int::ONE.to_odd().unwrap());
            odd_int_binxgcd_test(neg_max.to_odd().unwrap(), Int::MAX.to_odd().unwrap());
            odd_int_binxgcd_test(Int::ONE.to_odd().unwrap(), neg_max.to_odd().unwrap());
            odd_int_binxgcd_test(Int::ONE.to_odd().unwrap(), Int::MINUS_ONE.to_odd().unwrap());
            odd_int_binxgcd_test(Int::ONE.to_odd().unwrap(), Int::ONE.to_odd().unwrap());
            odd_int_binxgcd_test(Int::ONE.to_odd().unwrap(), Int::MAX.to_odd().unwrap());
            odd_int_binxgcd_test(Int::MAX.to_odd().unwrap(), neg_max.to_odd().unwrap());
            odd_int_binxgcd_test(Int::MAX.to_odd().unwrap(), Int::MINUS_ONE.to_odd().unwrap());
            odd_int_binxgcd_test(Int::MAX.to_odd().unwrap(), Int::ONE.to_odd().unwrap());
            odd_int_binxgcd_test(Int::MAX.to_odd().unwrap(), Int::MAX.to_odd().unwrap());

            for _ in 0..100 {
                let x = Odd::<Int<LIMBS>>::random(&mut OsRng);
                let y = Odd::<Int<LIMBS>>::random(&mut OsRng);
                odd_int_binxgcd_test(x, y);
            }
        }

        #[test]
        fn test_odd_int_binxgcd() {
            odd_int_binxgcd_tests::<{ U64::LIMBS }, { U128::LIMBS }>();
            odd_int_binxgcd_tests::<{ U128::LIMBS }, { U256::LIMBS }>();
            odd_int_binxgcd_tests::<{ U192::LIMBS }, { U384::LIMBS }>();
            odd_int_binxgcd_tests::<{ U256::LIMBS }, { U512::LIMBS }>();
            odd_int_binxgcd_tests::<{ U384::LIMBS }, { U768::LIMBS }>();
            odd_int_binxgcd_tests::<{ U512::LIMBS }, { U1024::LIMBS }>();
            odd_int_binxgcd_tests::<{ U1024::LIMBS }, { U2048::LIMBS }>();
            odd_int_binxgcd_tests::<{ U2048::LIMBS }, { U4096::LIMBS }>();
            odd_int_binxgcd_tests::<{ U4096::LIMBS }, { U8192::LIMBS }>();
        }
    }
}
