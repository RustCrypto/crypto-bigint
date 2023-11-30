//! Equivalence tests between `crypto_bigint::BoxedUint` and `num_bigint::BigUint`.

#![cfg(feature = "alloc")]

use core::cmp::Ordering;
use crypto_bigint::{BoxedUint, CheckedAdd, Limb, NonZero};
use num_bigint::{BigUint, ModInverse};
use proptest::prelude::*;

fn to_biguint(uint: &BoxedUint) -> BigUint {
    BigUint::from_bytes_be(&uint.to_be_bytes())
}

fn to_uint(big_uint: BigUint) -> BoxedUint {
    let bytes = big_uint.to_bytes_be();
    let pad_count = Limb::BYTES - (bytes.len() % Limb::BYTES);
    let mut padded_bytes = vec![0u8; pad_count];
    padded_bytes.extend_from_slice(&bytes);
    BoxedUint::from_be_slice(&padded_bytes, padded_bytes.len() * 8).unwrap()
}

fn reduce(x: &BoxedUint, n: &BoxedUint) -> BoxedUint {
    let bits_precision = n.bits_precision();
    let modulus = NonZero::new(n.clone()).expect("odd n");

    let x = match x.bits_precision().cmp(&bits_precision) {
        Ordering::Less => x.widen(bits_precision),
        Ordering::Equal => x.clone(),
        Ordering::Greater => x.shorten(bits_precision),
    };

    let x_reduced = x.rem_vartime(&modulus);
    debug_assert_eq!(x_reduced.bits_precision(), bits_precision);
    x_reduced
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
    /// Generate a pair of random `BoxedUint`s with the same precision.
    fn uint_pair()(mut a in uint(), mut b in uint()) -> (BoxedUint, BoxedUint) {
        if a.bits_precision() > b.bits_precision() {
            b = b.widen(a.bits_precision());
        } else if a.bits_precision() < b.bits_precision() {
            a = a.widen(b.bits_precision());
        }

        (a, b)
    }
}
prop_compose! {
    /// Generate a random odd modulus.
    fn modulus()(n in uint()) -> BoxedUint {
        if n.is_even().into() {
            n.wrapping_add(&BoxedUint::one())
        } else {
            n
        }
    }
}

proptest! {
    #[test]
    fn roundtrip(a in uint()) {
        prop_assert_eq!(&a, &to_uint(to_biguint(&a)));
    }

    #[test]
    fn checked_add(a in uint(), b in uint()) {
        let a_bi = to_biguint(&a);
        let b_bi = to_biguint(&b);
        let expected = a_bi + b_bi;

        match Option::<BoxedUint>::from(a.checked_add(&b)) {
            Some(actual) => prop_assert_eq!(expected, to_biguint(&actual)),
            None => {
                let max = BoxedUint::max(a.bits_precision());
                prop_assert!(expected > to_biguint(&max));
            }
        }
    }

    #[test]
    fn mod_inv((mut a, mut b) in uint_pair()) {
        if a.is_zero().into() {
            a = BoxedUint::one_with_precision(b.bits_precision());
        }

        if b.is_zero().into() {
            b = BoxedUint::one_with_precision(a.bits_precision());
        }

        let a_bi = to_biguint(&a);
        let b_bi = to_biguint(&b);
        let expected = a_bi.mod_inverse(b_bi);
        let actual = Option::from(a.inv_mod(&b));

        match (expected, actual) {
            (Some(exp), Some(act)) => prop_assert_eq!(exp, to_biguint(&act).into()),
            (None, None) => (),
            (_, _) => panic!("disagreement on if modular inverse exists")
        }
    }

    #[test]
    fn mul_mod(a in uint(), b in uint(), n in modulus()) {
        let a = reduce(&a, &n);
        let b = reduce(&b, &n);

        let a_bi = to_biguint(&a);
        let b_bi = to_biguint(&b);
        let n_bi = to_biguint(&n);

        let expected = to_uint((a_bi * b_bi) % n_bi);
        let actual = a.mul_mod(&b, &n);
        assert_eq!(expected, actual);
    }

    #[test]
    fn mul_wide(a in uint(), b in uint()) {
        let a_bi = to_biguint(&a);
        let b_bi = to_biguint(&b);

        let expected = a_bi * b_bi;
        let actual = a.mul(&b);

        prop_assert_eq!(expected, to_biguint(&actual));
    }

    #[test]
    fn rem_vartime((a, b) in uint_pair()) {
        if bool::from(!b.is_zero()) {
            let a_bi = to_biguint(&a);
            let b_bi = to_biguint(&b);

            let expected = a_bi % b_bi;
            let actual = a.rem_vartime(&NonZero::new(b).unwrap());

            prop_assert_eq!(expected, to_biguint(&actual));
        }
    }
}
