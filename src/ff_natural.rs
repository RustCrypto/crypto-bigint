use core::num::Wrapping;
use num_traits::{Num, Pow};
use crate::modular::runtime_mod::{DynResidue, DynResidueParams};
use crate::{Uint};

//// traits
// TODO: should I use crate::Pow or num_traits::Pow?
// I went with num_traits::Pow for consistency (because we also implement Num)
pub trait AsNaturalNumber<N: Num + Clone> {
    fn as_natural_number(&self) -> N;
    // TODO: maybe can return AsFiniteFieldElement, so that we can transition 2048->4096 here and do wide mul?
    // Or: we can have Mul return Output instead?
}

pub trait AsFiniteFieldElement<F: Num + Pow<F, Output = F> + Clone> {
    fn as_finite_field_element(&self, p: &Self) -> F;
}

//// Impl
// impl<const LIMBS: usize> AsNaturalNumber<Wrapping<Uint<LIMBS>>> for DynResidue<LIMBS> {
//     fn as_natural_number(&self) -> Wrapping<Uint<LIMBS>> {
//         Wrapping(self.retrieve())
//     }
// }
//
// impl<const LIMBS: usize> AsFiniteFieldElement<DynResidue<LIMBS>> for Wrapping<Uint<LIMBS>> {
//     fn as_finite_field_element(&self, p: &Self) -> DynResidue<LIMBS> {
//         let ff_params = DynResidueParams::new(&p.0);
//         DynResidue::new(&self.0, ff_params)
//     }
// }
//
// impl<const LIMBS: usize> AsNaturalNumber<Uint<LIMBS>> for DynResidue<LIMBS> {
//     fn as_natural_number(&self) -> Uint<LIMBS> {
//         self.retrieve()
//     }
// }
//
// impl<const LIMBS: usize> AsFiniteFieldElement<DynResidue<LIMBS>> for Uint<LIMBS> {
//     fn as_finite_field_element(&self, p: &Self) -> DynResidue<LIMBS> {
//         let ff_params = DynResidueParams::new(p);
//         DynResidue::new(self, ff_params)
//     }
// }

pub fn encrypt<N: Num, F: Num>(encryption_key: &N, plaintext: &N, randomness: &N) -> N
where
    N: AsFiniteFieldElement<F> + Clone,
    F: AsNaturalNumber<N> + Pow<F, Output = F> + Clone
{
    let n: N = encryption_key.clone();
    let n2 = n.clone() * n; // wrapping mul (N should be < 2048, T should be U4096);
    let n = encryption_key.as_finite_field_element(&n2);
    let m = plaintext.as_finite_field_element(&n2);
    let r = randomness.as_finite_field_element(&n2);
    let one = N::one().as_finite_field_element(&n2);

    ((m * n.clone() + one) * (r.pow(n))).as_natural_number()
}

pub fn decrypt<N: Num, F: Num>(decryption_key: &N, encryption_key: &N, ciphertext: &N) -> N
where
    N: AsFiniteFieldElement<F> + Clone,
    F: AsNaturalNumber<N> + Pow<F, Output = F> + Clone
{
    let n: N = encryption_key.clone();
    let n2 = n.clone() * n.clone(); // wrapping mul (N should be < 2048, T should be U4096);
    let d = decryption_key.as_finite_field_element(&n2);
    let c = ciphertext.as_finite_field_element(&n2);
    let one = N::one().as_finite_field_element(&n2);

    ((c.pow(d) - one).as_natural_number() // $ c^d - 1 mod N^2 $
        / n.clone()) // (c^d - 1 mod N^2) / n (division in N [Naturals])
        % n // Take mod N
}
