use core::ops::MulAssign;

use crate::{Concat, Split, UInt};

use super::{montgomery_reduction, Residue, ResidueParams};

impl<MOD: ResidueParams<LIMBS>, const LIMBS: usize, const DLIMBS: usize> Residue<MOD, LIMBS>
where
    UInt<LIMBS>: Concat<Output = UInt<DLIMBS>>,
    UInt<DLIMBS>: Split<Output = UInt<LIMBS>>,
{
    pub fn square(&mut self) {
        let (hi, lo) = self.montgomery_form.square().split();
        self.montgomery_form = montgomery_reduction::<MOD, LIMBS>((lo, hi));
    }
}

impl<MOD: ResidueParams<LIMBS>, const LIMBS: usize> MulAssign for Residue<MOD, LIMBS> {
    fn mul_assign(&mut self, rhs: Self) {
        let product = self.montgomery_form.mul_wide(&rhs.montgomery_form);
        self.montgomery_form = montgomery_reduction::<MOD, LIMBS>(product);
    }
}
