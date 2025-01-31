//! This module implements (a constant variant of) the Optimized Extended Binary GCD algorithm,
//! which is described by Pornin as Algorithm 2 in "Optimized Binary GCD for Modular Inversion".
//! Ref: <https://eprint.iacr.org/2020/972.pdf>

use crate::Uint;

mod extension;
mod gcd;
mod matrix;
mod tools;

mod xgcd;

impl<const LIMBS: usize> Uint<LIMBS> {
    /// Compute the greatest common divisor of `self` and `rhs`.
    pub const fn bingcd(&self, rhs: &Self) -> Self {
        let self_is_zero = self.is_nonzero().not();
        let self_nz = Uint::select(self, &Uint::ONE, self_is_zero)
            .to_nz()
            .expect("self is non zero by construction");
        Uint::select(&self_nz.bingcd(rhs), rhs, self_is_zero)
    }
}

#[cfg(feature = "rand_core")]
#[cfg(test)]
mod tests {
    use rand_core::OsRng;

    use crate::{Gcd, Random, Uint, U1024, U16384, U2048, U256, U4096, U512, U8192};

    fn gcd_comparison_test<const LIMBS: usize>(lhs: Uint<LIMBS>, rhs: Uint<LIMBS>)
    where
        Uint<LIMBS>: Gcd<Output = Uint<LIMBS>>,
    {
        let gcd = lhs.gcd(&rhs);
        let bingcd = lhs.bingcd(&rhs);
        assert_eq!(gcd, bingcd);
    }

    fn test_bingcd<const LIMBS: usize>()
    where
        Uint<LIMBS>: Gcd<Output = Uint<LIMBS>>,
    {
        // some basic test
        gcd_comparison_test(Uint::ZERO, Uint::ZERO);
        gcd_comparison_test(Uint::ZERO, Uint::ONE);
        gcd_comparison_test(Uint::ZERO, Uint::MAX);
        gcd_comparison_test(Uint::ONE, Uint::ZERO);
        gcd_comparison_test(Uint::ONE, Uint::ONE);
        gcd_comparison_test(Uint::ONE, Uint::MAX);
        gcd_comparison_test(Uint::MAX, Uint::ZERO);
        gcd_comparison_test(Uint::MAX, Uint::ONE);
        gcd_comparison_test(Uint::MAX, Uint::MAX);

        for _ in 0..100 {
            let x = Uint::<LIMBS>::random(&mut OsRng);
            let mut y = Uint::<LIMBS>::random(&mut OsRng);

            y = Uint::select(&(y.wrapping_add(&Uint::ONE)), &y, y.is_odd());

            gcd_comparison_test(x, y);
        }
    }

    #[test]
    fn testing() {
        test_bingcd::<{ U256::LIMBS }>();
        test_bingcd::<{ U512::LIMBS }>();
        test_bingcd::<{ U1024::LIMBS }>();
        test_bingcd::<{ U2048::LIMBS }>();
        test_bingcd::<{ U4096::LIMBS }>();
        test_bingcd::<{ U8192::LIMBS }>();
        test_bingcd::<{ U16384::LIMBS }>();
    }
}
