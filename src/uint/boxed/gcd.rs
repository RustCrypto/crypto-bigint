//! Support for computing greatest common divisor of two `BoxedUint`s.

use super::BoxedUint;
use crate::{modular::safegcd, ConstantTimeSelect, Gcd, Integer, Odd};
use subtle::{ConditionallySelectable, ConstantTimeLess};

impl Gcd for BoxedUint {
    type Output = Self;

    /// Compute the greatest common divisor (GCD) of this number and another.
    fn gcd(&self, rhs: &Self) -> Self {
        let k1 = self.trailing_zeros();
        let k2 = rhs.trailing_zeros();

        // Select the smaller of the two `k` values, making 2^k the common even divisor
        let k = u32::conditional_select(&k1, &k2, u32::ct_lt(&k2, &k1));

        // Decompose `self` and `rhs` into `s{1, 2} * 2^k` where either `s1` or `s2` is odd
        let s1 = self.overflowing_shr(k).0;
        let s2 = rhs.overflowing_shr(k).0;

        let f = Self::ct_select(&s1, &s2, !s2.is_odd());
        let g = Self::ct_select(&s1, &s2, s2.is_odd());
        safegcd::boxed::gcd(&f, &g).overflowing_shl(k).0
    }

    fn gcd_vartime(&self, rhs: &Self) -> Self::Output {
        match Odd::<Self>::new(self.clone()).into_option() {
            Some(odd) => odd.gcd_vartime(rhs),
            None => self.gcd(rhs), // TODO(tarcieri): vartime support for even `self`?
        }
    }
}

impl Gcd<BoxedUint> for Odd<BoxedUint> {
    type Output = BoxedUint;

    fn gcd(&self, rhs: &BoxedUint) -> BoxedUint {
        safegcd::boxed::gcd(self, rhs)
    }

    fn gcd_vartime(&self, rhs: &BoxedUint) -> Self::Output {
        safegcd::boxed::gcd_vartime(self, rhs)
    }
}

#[cfg(test)]
mod tests {
    use crate::{BoxedUint, Gcd};

    #[test]
    fn gcd_relatively_prime() {
        // Two semiprimes with no common factors
        let f = BoxedUint::from(59u32 * 67).to_odd().unwrap();
        let g = BoxedUint::from(61u32 * 71);
        let gcd = f.gcd(&g);
        assert_eq!(gcd, BoxedUint::one());
    }

    #[test]
    fn gcd_nonprime() {
        let f = BoxedUint::from(4391633u32).to_odd().unwrap();
        let g = BoxedUint::from(2022161u32);
        let gcd = f.gcd(&g);
        assert_eq!(gcd, BoxedUint::from(1763u32));
    }

    #[test]
    fn gcd_zero() {
        let zero = BoxedUint::from(0u32);
        let one = BoxedUint::from(1u32);

        assert_eq!(zero.gcd(&zero), zero);
        assert_eq!(zero.gcd(&one), one);
        assert_eq!(one.gcd(&zero), one);
    }

    #[test]
    fn gcd_one() {
        let f = BoxedUint::from(1u32);
        assert_eq!(BoxedUint::from(1u32), f.gcd(&BoxedUint::from(1u32)));
        assert_eq!(BoxedUint::from(1u32), f.gcd(&BoxedUint::from(2u8)));
    }

    #[test]
    fn gcd_two() {
        let f = BoxedUint::from(2u32);
        assert_eq!(f, f.gcd(&f));

        let g = BoxedUint::from(4u32);
        assert_eq!(f, f.gcd(&g));
        assert_eq!(f, g.gcd(&f));
    }

    #[test]
    fn gcd_different_sizes() {
        // Test that gcd works for boxed Uints with different numbers of limbs
        let f = BoxedUint::from(4391633u32).widen(128).to_odd().unwrap();
        let g = BoxedUint::from(2022161u32);
        let gcd = f.gcd(&g);
        assert_eq!(gcd, BoxedUint::from(1763u32));
    }

    #[test]
    fn gcd_vartime_different_sizes() {
        // Test that gcd works for boxed Uints with different numbers of limbs
        let f = BoxedUint::from(4391633u32).widen(128).to_odd().unwrap();
        let g = BoxedUint::from(2022161u32);
        let gcd = f.gcd_vartime(&g);
        assert_eq!(gcd, BoxedUint::from(1763u32));
    }
}
