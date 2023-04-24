use crate::Wrapping;
use crate::modular::runtime_mod::{DynResidue, DynResidueParams};
use crate::{AsNaturalNumber, AsRingElement, Uint};

impl<const LIMBS: usize> num_traits::Pow<DynResidue<LIMBS>> for DynResidue<LIMBS>{
    type Output = DynResidue<LIMBS>;

    fn pow(self, rhs: DynResidue<LIMBS>) -> Self::Output {
        // self.pow(&rhs.retrieve()) // TODO: can't, because these are the same name
        self.pow_bounded_exp(&rhs.retrieve(), Uint::<LIMBS>::BITS)
    }
}

impl<const LIMBS: usize> AsNaturalNumber<Wrapping<Uint<LIMBS>>> for DynResidue<LIMBS> {
    fn as_natural_number(&self) -> Wrapping<Uint<LIMBS>> {
        Wrapping(self.retrieve())
    }
}

impl<const LIMBS: usize> AsRingElement<DynResidue<LIMBS>> for Wrapping<Uint<LIMBS>> {
    fn as_ring_element(&self, p: &Self) -> DynResidue<LIMBS> {
        let ring_params = DynResidueParams::new(&p.0);
        DynResidue::new(&self.0, ring_params)
    }
}
