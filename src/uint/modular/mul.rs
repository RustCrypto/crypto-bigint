use core::ops::MulAssign;

use crate::{Concat, Split, UInt};

use super::{montgomery_reduction, Modular};

impl<const LIMBS: usize, const DLIMBS: usize> Modular<LIMBS>
where
    UInt<LIMBS>: Concat<Output = UInt<DLIMBS>>,
    UInt<DLIMBS>: Split<Output = UInt<LIMBS>>,
{
    pub fn square(&mut self) {
        let (hi, lo) = self.value.square().split();
        self.value = montgomery_reduction((lo, hi), &self.modulus_params);
    }
}

impl<const LIMBS: usize> MulAssign for Modular<LIMBS> {
    fn mul_assign(&mut self, rhs: Self) {
        let product = self.value.mul_wide(&rhs.value);
        self.value = montgomery_reduction(product, &self.modulus_params);
    }
}
