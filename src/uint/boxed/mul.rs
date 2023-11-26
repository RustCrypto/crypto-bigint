//! [`BoxedUint`] multiplication operations.

use crate::{BoxedUint, Limb};

impl BoxedUint {
    /// Multiply `self` by `rhs`.
    pub fn mul_wide(&self, rhs: &Self) -> Self {
        let mut ret = Self {
            limbs: vec![Limb::ZERO; self.nlimbs() + rhs.nlimbs()].into(),
        };

        // Schoolbook multiplication.
        // TODO(tarcieri): use Karatsuba for better performance? Share impl with `Uint::mul`?
        for i in 0..self.nlimbs() {
            let mut carry = Limb::ZERO;

            for j in 0..rhs.nlimbs() {
                let k = i + j;
                let (n, c) = ret.limbs[k].mac(self.limbs[i], rhs.limbs[j], carry);
                ret.limbs[k] = n;
                carry = c;
            }

            ret.limbs[i + rhs.nlimbs()] = carry;
        }

        ret
    }

    /// Multiply `self` by itself.
    pub fn square(&self) -> Self {
        // TODO(tarcieri): more optimized implementation
        self.mul_wide(self)
    }
}

#[cfg(test)]
mod tests {
    use crate::BoxedUint;

    #[test]
    fn mul_zero_and_one() {
        assert!(bool::from(
            BoxedUint::zero().mul_wide(&BoxedUint::zero()).is_zero()
        ));
        assert!(bool::from(
            BoxedUint::zero().mul_wide(&BoxedUint::one()).is_zero()
        ));
        assert!(bool::from(
            BoxedUint::one().mul_wide(&BoxedUint::zero()).is_zero()
        ));
        assert_eq!(
            BoxedUint::one().mul_wide(&BoxedUint::one()),
            BoxedUint::one()
        );
    }

    #[test]
    fn mul_primes() {
        let primes: &[u32] = &[3, 5, 17, 257, 65537];

        for &a_int in primes {
            for &b_int in primes {
                let actual = BoxedUint::from(a_int).mul_wide(&BoxedUint::from(b_int));
                let expected = BoxedUint::from(a_int as u64 * b_int as u64);
                assert_eq!(actual, expected);
            }
        }
    }
}
