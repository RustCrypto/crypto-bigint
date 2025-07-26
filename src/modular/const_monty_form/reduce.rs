use crate::{modular::ConstMontyForm, Reduce, Uint};

use super::ConstMontyParams;

impl<const LIMBS: usize, MOD> Reduce<Uint<LIMBS>> for ConstMontyForm<MOD, LIMBS>
where
    MOD: ConstMontyParams<LIMBS>
{
    fn reduce(value: Uint<LIMBS>) -> Self {
        Self::new(&value)
    }
}

impl<const LIMBS: usize, MOD> Reduce<&Uint<LIMBS>> for ConstMontyForm<MOD, LIMBS>
where
    MOD: ConstMontyParams<LIMBS>
{
    fn reduce(value: &Uint<LIMBS>) -> Self {
        Self::new(value)
    }
}
