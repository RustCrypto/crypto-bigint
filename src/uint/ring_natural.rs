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

pub fn encrypt<N: num_traits::Num, F: num_traits::Num>(encryption_key: &N, plaintext: &N, randomness: &N) -> N
    where
        N: AsRingElement<F> + Clone,
        F: AsNaturalNumber<N> + num_traits::Pow<F, Output = F> + Clone
{
    let n: N = encryption_key.clone();
    let n2 = n.clone() * n; // wrapping mul (N should be < 2048, T should be U4096);
    let n = encryption_key.as_ring_element(&n2);
    let m = plaintext.as_ring_element(&n2);
    let r = randomness.as_ring_element(&n2);
    let one = N::one().as_ring_element(&n2);

    ((m * n.clone() + one) * (r.pow(n))).as_natural_number()
}

pub fn decrypt<N: num_traits::Num, F: num_traits::Num>(decryption_key: &N, encryption_key: &N, ciphertext: &N) -> N
    where
        N: AsRingElement<F> + Clone,
        F: AsNaturalNumber<N> + num_traits::Pow<F, Output = F> + Clone
{
    let n: N = encryption_key.clone();
    let n2 = n.clone() * n.clone(); // wrapping mul (N should be < 2048, T should be U4096);
    let d = decryption_key.as_ring_element(&n2);
    let c = ciphertext.as_ring_element(&n2);
    let one = N::one().as_ring_element(&n2);

    ((c.pow(d) - one).as_natural_number() // $ c^d - 1 mod N^2 $
        / n.clone()) // (c^d - 1 mod N^2) / n (division in N [Naturals])
        % n // Take mod N
}
