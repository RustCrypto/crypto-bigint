//! Support for computing greatest common divisor of two `BoxedUint`s.

use super::BoxedUint;
use crate::{modular::bernstein_yang, Odd};

impl Odd<BoxedUint> {
    /// Compute the greatest common divisor (GCD) of this number and another.
    pub fn gcd(&self, rhs: &BoxedUint) -> BoxedUint {
        bernstein_yang::boxed::gcd(self, rhs)
    }
}

#[cfg(test)]
mod tests {
    use crate::BoxedUint;

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
}
