//! Support for computing the greatest common divisor of two `Uint`s.

use crate::{modular::SafeGcdInverter, ConstChoice, Gcd, Odd, PrecomputeInverter, Uint};

impl<const SAT_LIMBS: usize, const UNSAT_LIMBS: usize> Uint<SAT_LIMBS>
where
    Odd<Self>: PrecomputeInverter<Inverter = SafeGcdInverter<SAT_LIMBS, UNSAT_LIMBS>>,
{
    /// Compute the greatest common divisor (GCD) of this number and another.
    ///
    /// Runs in a constant number of iterations depending on the maximum highest bit of either
    /// `self` or `rhs`.
    pub const fn gcd(&self, rhs: &Self) -> Self {
        let k1 = self.trailing_zeros();
        let k2 = rhs.trailing_zeros();

        // Select the smaller of the two `k` values, making 2^k the common even divisor
        let k = ConstChoice::from_u32_lt(k2, k1).select_u32(k1, k2);

        // Decompose `self` and `rhs` into `s{1, 2} * 2^k` where either `s1` or `s2` is odd
        let s1 = self.overflowing_shr(k).unwrap_or(Self::ZERO);
        let s2 = rhs.overflowing_shr(k).unwrap_or(Self::ZERO);

        let f = Self::select(&s1, &s2, s2.is_odd().not());
        let g = Self::select(&s1, &s2, s2.is_odd());

        <Odd<Self> as PrecomputeInverter>::Inverter::gcd(&f, &g)
            .overflowing_shl(k)
            .unwrap_or(Self::ZERO)
    }
}

impl<const SAT_LIMBS: usize, const UNSAT_LIMBS: usize> Odd<Uint<SAT_LIMBS>>
where
    Self: PrecomputeInverter<Inverter = SafeGcdInverter<SAT_LIMBS, UNSAT_LIMBS>>,
{
    /// Compute the greatest common divisor (GCD) of this number and another.
    ///
    /// Runs in variable time with respect to `rhs`.
    pub const fn gcd_vartime(&self, rhs: &Uint<SAT_LIMBS>) -> Uint<SAT_LIMBS> {
        <Self as PrecomputeInverter>::Inverter::gcd_vartime(self.as_ref(), rhs)
    }
}

impl<const SAT_LIMBS: usize, const UNSAT_LIMBS: usize> Gcd for Uint<SAT_LIMBS>
where
    Odd<Self>: PrecomputeInverter<Inverter = SafeGcdInverter<SAT_LIMBS, UNSAT_LIMBS>>,
{
    type Output = Uint<SAT_LIMBS>;

    fn gcd(&self, rhs: &Self) -> Self {
        self.gcd(rhs)
    }

    fn gcd_vartime(&self, rhs: &Self) -> Self::Output {
        match Odd::<Self>::new(*self).into_option() {
            Some(odd) => odd.gcd_vartime(rhs),
            None => self.gcd(rhs), // TODO(tarcieri): vartime support for even `self`?
        }
    }
}

impl<const SAT_LIMBS: usize, const UNSAT_LIMBS: usize> Gcd<Uint<SAT_LIMBS>> for Odd<Uint<SAT_LIMBS>>
where
    Odd<Self>: PrecomputeInverter<Inverter = SafeGcdInverter<SAT_LIMBS, UNSAT_LIMBS>>,
{
    type Output = Uint<SAT_LIMBS>;

    fn gcd(&self, rhs: &Uint<SAT_LIMBS>) -> Uint<SAT_LIMBS> {
        <Odd<Self> as PrecomputeInverter>::Inverter::gcd(self, rhs)
    }

    fn gcd_vartime(&self, rhs: &Uint<SAT_LIMBS>) -> Self::Output {
        <Odd<Self> as PrecomputeInverter>::Inverter::gcd_vartime(self, rhs)
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
    fn gcd_zero() {
        assert_eq!(U256::ZERO.gcd(&U256::ZERO), U256::ZERO);
        assert_eq!(U256::ZERO.gcd(&U256::ONE), U256::ONE);
        assert_eq!(U256::ONE.gcd(&U256::ZERO), U256::ONE);
    }

    #[test]
    fn gcd_one() {
        let f = U256::ONE;
        assert_eq!(U256::ONE, f.gcd(&U256::ONE));
        assert_eq!(U256::ONE, f.gcd(&U256::from(2u8)));
    }

    #[test]
    fn gcd_two() {
        let f = U256::from_u8(2);
        assert_eq!(f, f.gcd(&f));

        let g = U256::from_u8(4);
        assert_eq!(f, f.gcd(&g));
        assert_eq!(f, g.gcd(&f));
    }
}
