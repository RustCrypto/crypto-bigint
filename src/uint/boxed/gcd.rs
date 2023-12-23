//! Support for computing greatest common divisor of two `BoxedUint`s.

use super::BoxedUint;
use crate::{modular::bernstein_yang, Gcd, Integer, Odd};
use subtle::CtOption;

impl Gcd for BoxedUint {
    type Output = CtOption<Self>;

    fn gcd(&self, rhs: &Self) -> CtOption<Self> {
        let ret = bernstein_yang::boxed::gcd(self, rhs);
        CtOption::new(ret, self.is_odd())
    }
}

impl Gcd<BoxedUint> for Odd<BoxedUint> {
    type Output = BoxedUint;

    fn gcd(&self, rhs: &BoxedUint) -> BoxedUint {
        bernstein_yang::boxed::gcd(self, rhs)
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
}
