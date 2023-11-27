//! Equivalence tests between `crypto_bigint::BoxedUint` and `num-bigint`.

#![cfg(feature = "alloc")]

use crypto_bigint::{
    modular::{BoxedResidue, BoxedResidueParams},
    BoxedUint, Limb,
};
use num_bigint::BigUint;
use proptest::prelude::*;
use std::cmp::Ordering;

fn to_biguint(uint: &BoxedUint) -> BigUint {
    BigUint::from_bytes_be(&uint.to_be_bytes())
}

fn retrieve_biguint(residue: &BoxedResidue) -> BigUint {
    to_biguint(&residue.retrieve())
}

prop_compose! {
    /// Generate a random `BoxedUint`.
    fn uint()(mut bytes in any::<Vec<u8>>()) -> BoxedUint {
        let extra = bytes.len() % Limb::BYTES;
        let bytes_precision = bytes.len() - extra;
        bytes.truncate(bytes_precision);
        BoxedUint::from_be_slice(&bytes, bytes_precision * 8).unwrap()
    }
}
prop_compose! {
    /// Generate a random modulus.
    fn modulus()(mut a in uint()) -> BoxedResidueParams {
        if a.is_even().into() {
            a = a.wrapping_add(&BoxedUint::one());
        }

        BoxedResidueParams::new(a).expect("modulus should be valid")
    }
}
prop_compose! {
    /// Generate two residues with a common modulus.
    fn residue_pair()(a in uint(), b in uint(), p in modulus()) -> (BoxedResidue, BoxedResidue) {
        fn reduce(n: &BoxedUint, p: BoxedResidueParams) -> BoxedResidue {
            let bits_precision = p.modulus().bits_precision();

            let n = match n.bits_precision().cmp(&bits_precision) {
                Ordering::Less => n.widen(bits_precision),
                Ordering::Equal => n.clone(),
                Ordering::Greater => n.shorten(bits_precision)
            };

            let n_reduced = n.rem_vartime(&p.modulus()).unwrap().widen(p.bits_precision());
            BoxedResidue::new(&n_reduced, p)
        }


        (reduce(&a, p.clone()), reduce(&b, p.clone()))
    }
}

proptest! {
    #[test]
    fn mul((a, b) in residue_pair()) {
        let p = a.params().modulus();
        let c = &a * &b;

        let a_bi = retrieve_biguint(&a);
        let b_bi = retrieve_biguint(&b);
        let p_bi = to_biguint(&p);
        let c_bi = (a_bi * b_bi) % p_bi;

        prop_assert_eq!(retrieve_biguint(&c), c_bi);
    }
}
