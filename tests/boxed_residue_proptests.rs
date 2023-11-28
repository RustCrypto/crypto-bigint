//! Equivalence tests between `crypto_bigint::BoxedUint` and `num-bigint`.

#![cfg(feature = "alloc")]

use crypto_bigint::{
    modular::{BoxedResidue, BoxedResidueParams},
    BoxedUint, Limb, NonZero,
};
use num_bigint::{BigUint, ModInverse};
use proptest::prelude::*;
use std::cmp::Ordering;

fn to_biguint(uint: &BoxedUint) -> BigUint {
    BigUint::from_bytes_be(&uint.to_be_bytes())
}

fn retrieve_biguint(residue: &BoxedResidue) -> BigUint {
    to_biguint(&residue.retrieve())
}

fn reduce(n: &BoxedUint, p: BoxedResidueParams) -> BoxedResidue {
    let bits_precision = p.modulus().bits_precision();
    let modulus = NonZero::new(p.modulus().clone()).unwrap();

    let n = match n.bits_precision().cmp(&bits_precision) {
        Ordering::Less => n.widen(bits_precision),
        Ordering::Equal => n.clone(),
        Ordering::Greater => n.shorten(bits_precision),
    };

    let n_reduced = n.rem_vartime(&modulus).widen(p.bits_precision());
    BoxedResidue::new(&n_reduced, p)
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
    /// Generate a random odd modulus.
    fn modulus()(mut n in uint()) -> BoxedResidueParams {
        if n.is_even().into() {
            n = n.wrapping_add(&BoxedUint::one());
        }

        BoxedResidueParams::new(n).expect("modulus should be valid")
    }
}
prop_compose! {
    /// Generate two residues with a common modulus.
    fn residue_pair()(a in uint(), b in uint(), n in modulus()) -> (BoxedResidue, BoxedResidue) {
        (reduce(&a, n.clone()), reduce(&b, n.clone()))
    }
}

proptest! {
    #[test]
    fn inv(x in uint(), n in modulus()) {
        let x = reduce(&x, n.clone());
        let actual = Option::<BoxedResidue>::from(x.invert()).map(|a| a.retrieve());

        let x_bi = retrieve_biguint(&x);
        let n_bi = to_biguint(n.modulus());
        let expected = x_bi.mod_inverse(&n_bi);

        match (expected, actual) {
            (Some(exp), Some(act)) => prop_assert_eq!(exp, to_biguint(&act).into()),
            (None, None) => (),
            (_, _) => panic!("disagreement on if modular inverse exists")
        }
    }

    #[test]
    fn mul((a, b) in residue_pair()) {
        let p = a.params().modulus();
        let actual = &a * &b;

        let a_bi = retrieve_biguint(&a);
        let b_bi = retrieve_biguint(&b);
        let p_bi = to_biguint(&p);
        let expected = (a_bi * b_bi) % p_bi;

        prop_assert_eq!(retrieve_biguint(&actual), expected);
    }

    #[test]
    fn pow(a in uint(), b in uint(), n in modulus()) {
        let a = reduce(&a, n.clone());
        let actual = a.pow(&b);

        let a_bi = retrieve_biguint(&a);
        let b_bi = to_biguint(&b);
        let n_bi = to_biguint(n.modulus());
        let expected = a_bi.modpow(&b_bi, &n_bi);

        prop_assert_eq!(retrieve_biguint(&actual), expected);
    }
}
