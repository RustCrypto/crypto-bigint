//! [`Uint`] exponentiation operations.

use super::Uint;
use crate::CtOption;

impl<const LIMBS: usize> Uint<LIMBS> {
    /// Computes `self^exp`, returning a `CtOption` which is none in the case of overflow.
    ///
    /// This method is variable time in the exponent `exp`.
    pub fn checked_pow_vartime(&self, exp: u32) -> CtOption<Self> {
        if exp == 0 {
            return CtOption::some(Self::ONE);
        }
        let bits = u32::BITS - exp.leading_zeros();
        let mut ret = CtOption::some(*self);
        let mut i = bits - 1;
        while i > 0 {
            i -= 1;
            ret = ret.and_then(|ret| ret.checked_square());
            if (exp >> i) & 1 == 1 {
                ret = ret.and_then(|ret| ret.checked_mul(self));
            }
        }
        ret
    }

    /// Computes `self^exp`.
    ///
    /// This method is variable time in the exponent `exp`.
    pub const fn wrapping_pow_vartime(&self, exp: u32) -> Self {
        if exp == 0 {
            return Self::ONE;
        }
        let bits = u32::BITS - exp.leading_zeros();
        let mut ret = *self;
        let mut i = bits - 1;
        while i > 0 {
            i -= 1;
            ret = ret.wrapping_square();
            if (exp >> i) & 1 == 1 {
                ret = ret.wrapping_mul(self);
            }
        }
        ret
    }
}

#[cfg(test)]
mod tests {
    use crate::U256;

    #[test]
    fn checked_pow_expected() {
        assert_eq!(
            U256::ZERO.checked_pow_vartime(0).into_option(),
            Some(U256::ONE)
        );
        assert_eq!(
            U256::ONE.checked_pow_vartime(0).into_option(),
            Some(U256::ONE)
        );
        assert_eq!(
            U256::MAX.checked_pow_vartime(0).into_option(),
            Some(U256::ONE)
        );
        assert_eq!(
            U256::MAX.checked_pow_vartime(1).into_option(),
            Some(U256::MAX)
        );
        assert_eq!(U256::MAX.checked_pow_vartime(2).into_option(), None);
    }

    #[test]
    fn wrapping_pow_expected() {
        assert_eq!(U256::ZERO.wrapping_pow_vartime(0), U256::ONE);
        assert_eq!(U256::ONE.wrapping_pow_vartime(0), U256::ONE);

        for exp in 1..10 {
            assert_eq!(
                U256::ZERO.wrapping_pow_vartime(exp),
                U256::ZERO,
                "exp={exp}"
            );
            assert_eq!(U256::ONE.wrapping_pow_vartime(exp), U256::ONE, "exp={exp}");
        }

        let two = U256::from_u8(2);
        assert_eq!(two.wrapping_pow_vartime(0), U256::ONE);
        assert_eq!(two.wrapping_pow_vartime(1), two);
        assert_eq!(two.wrapping_pow_vartime(2), U256::from_u8(4));
        assert_eq!(two.wrapping_pow_vartime(3), U256::from_u8(8));
        assert_eq!(two.wrapping_pow_vartime(4), U256::from_u8(16));

        assert_eq!(U256::MAX.wrapping_pow_vartime(0), U256::ONE);
        assert_eq!(U256::MAX.wrapping_pow_vartime(1), U256::MAX);
        assert_eq!(U256::MAX.wrapping_pow_vartime(2), U256::ONE);
        assert_eq!(U256::MAX.wrapping_pow_vartime(3), U256::MAX);
    }
}
