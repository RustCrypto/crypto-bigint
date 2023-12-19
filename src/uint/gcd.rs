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
    pub fn gcd(&self, rhs: &Self) -> Self {
        debug_assert!(bool::from(self.is_odd()));
        <Self as PrecomputeInverter>::Inverter::gcd(self, rhs)
    }
}

#[cfg(test)]
mod tests {
    use crate::U256;

    #[test]
    fn gcd() {
        let f = U256::from(4391633u32);
        let g = U256::from(2022161u32);
        let gcd = f.gcd(&g);
        assert_eq!(gcd, U256::from(1763u32));
    }
}
