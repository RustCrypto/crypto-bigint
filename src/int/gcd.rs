//! Support for computing the greatest common divisor of `Int`s.

use crate::{Gcd, Int, Odd, PrecomputeInverter, Uint};
use crate::modular::SafeGcdInverter;

/// Gcd of two [Int]s
impl<const SAT_LIMBS: usize, const UNSAT_LIMBS: usize> Gcd for Int<SAT_LIMBS>
where
    Odd<Uint<SAT_LIMBS>>: PrecomputeInverter<Inverter=SafeGcdInverter<SAT_LIMBS, UNSAT_LIMBS>>,
{
    type Output = Uint<SAT_LIMBS>;

    fn gcd(&self, rhs: &Self) -> Self::Output {
        self.abs().gcd(&rhs.abs())
    }

    fn gcd_vartime(&self, rhs: &Self) -> Self::Output {
        self.abs().gcd_vartime(&rhs.abs())
    }
}

/// Gcd of an [Int] and a [Uint].
impl<const SAT_LIMBS: usize, const UNSAT_LIMBS: usize> Gcd<Uint<SAT_LIMBS>> for Int<SAT_LIMBS>
where
    Odd<Uint<SAT_LIMBS>>: PrecomputeInverter<Inverter=SafeGcdInverter<SAT_LIMBS, UNSAT_LIMBS>>,
{
    type Output = Uint<SAT_LIMBS>;

    fn gcd(&self, rhs: &Uint<SAT_LIMBS>) -> Self::Output {
        self.abs().gcd(&rhs)
    }

    fn gcd_vartime(&self, rhs: &Uint<SAT_LIMBS>) -> Self::Output {
        self.abs().gcd_vartime(rhs)
    }
}

#[cfg(test)]
mod tests {
    use crate::{Gcd, I256, U256};

    #[test]
    fn gcd_always_positive() {
        // Two numbers with a shared factor of 61
        let f = I256::from(59i32 * 61);
        let g = I256::from(61i32 * 71);

        assert_eq!(U256::from(61u32), f.gcd(&g));
        assert_eq!(U256::from(61u32), f.wrapping_neg().gcd(&g));
        assert_eq!(U256::from(61u32), f.gcd(&g.wrapping_neg()));
        assert_eq!(U256::from(61u32), f.wrapping_neg().gcd(&g.wrapping_neg()));
    }

    #[test]
    fn gcd_int_uint() {
        // Two numbers with a shared factor of 61
        let f = I256::from(59i32 * 61);
        let g = U256::from(61u32 * 71);

        assert_eq!(U256::from(61u32), f.gcd(&g));
        assert_eq!(U256::from(61u32), f.wrapping_neg().gcd(&g));
    }
}