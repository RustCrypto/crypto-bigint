use core::ops::MulAssign;

use crate::UInt;

use super::{montgomery_reduction, Modular};

impl<const LIMBS: usize> MulAssign<&UInt<LIMBS>> for Modular<LIMBS> {
    fn mul_assign(&mut self, rhs: &UInt<LIMBS>) {
        let product = self.value.mul_wide(rhs);
        self.value = montgomery_reduction(product, &self.modulus_params);
    }
}

impl<const LIMBS: usize> MulAssign for Modular<LIMBS> {
    fn mul_assign(&mut self, rhs: Self) {
        self.mul_assign(&rhs.value);
    }
}
