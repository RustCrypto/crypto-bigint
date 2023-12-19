//! Support for computing greatest common divisor of two `Uint`s.

use super::Uint;
use crate::{modular::BernsteinYangInverter, PrecomputeInverter};

impl<const SAT_LIMBS: usize, const UNSAT_LIMBS: usize> Uint<SAT_LIMBS>
where
    Self: PrecomputeInverter<Inverter = BernsteinYangInverter<SAT_LIMBS, UNSAT_LIMBS>>,
{
    /// Compute the greatest common divisor (GCD) of this number and another.
    ///
    /// Panics if `self` is odd.
    pub const fn gcd(&self, rhs: &Self) -> Self {
        debug_assert!(self.is_odd().is_true_vartime());
        <Self as PrecomputeInverter>::Inverter::gcd(self, rhs)
    }
}

#[cfg(test)]
mod tests {
    use crate::U256;

    #[test]
    fn gcd_relatively_prime() {
        // Two semiprimes with no common factors
        let f = U256::from(59u32 * 67);
        let g = U256::from(61u32 * 71);
        let gcd = f.gcd(&g);
        assert_eq!(gcd, U256::ONE);
    }

    #[test]
    fn gcd_nonprime() {
        let f = U256::from(4391633u32);
        let g = U256::from(2022161u32);
        let gcd = f.gcd(&g);
        assert_eq!(gcd, U256::from(1763u32));
    }

    #[test]
    fn gcd_one() {
        let f = U256::ONE;
        assert_eq!(U256::ONE, f.gcd(&U256::ONE));
        assert_eq!(U256::ONE, f.gcd(&U256::from(2u8)));
    }
}
