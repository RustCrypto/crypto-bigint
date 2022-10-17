use core::{marker::PhantomData, ops::MulAssign};

use crate::{Concat, Split, UInt};

use super::{montgomery_reduction, Residue, ResidueParams};

impl<MOD: ResidueParams<LIMBS>, const LIMBS: usize> Residue<MOD, LIMBS> {
    /// Computes the (reduced) product between two residues.
    pub const fn mul(&self, rhs: &Self) -> Self {
        let product = self.montgomery_form.mul_wide(&rhs.montgomery_form);
        let montgomery_form = montgomery_reduction::<MOD, LIMBS>(product);

        Self {
            montgomery_form,
            phantom: PhantomData,
        }
    }
}

impl<MOD: ResidueParams<LIMBS>, const LIMBS: usize, const DLIMBS: usize> Residue<MOD, LIMBS>
where
    UInt<LIMBS>: Concat<Output = UInt<DLIMBS>>,
    UInt<DLIMBS>: Split<Output = UInt<LIMBS>>,
{
    /// Computes the (reduced) square of a residue.
    pub fn square(&mut self) {
        let (hi, lo) = self.montgomery_form.square().split();
        self.montgomery_form = montgomery_reduction::<MOD, LIMBS>((lo, hi));
    }
}

impl<MOD: ResidueParams<LIMBS>, const LIMBS: usize> MulAssign for Residue<MOD, LIMBS> {
    fn mul_assign(&mut self, rhs: Self) {
        *self = self.mul(&rhs)
    }
}
