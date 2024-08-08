//! Equivalence tests between `crypto_bigint::BoxedMontyForm` and `num-bigint`.

#![cfg(feature = "alloc")]

mod common;

use common::to_biguint;
use crypto_bigint::{
    modular::{BoxedMontyForm, BoxedMontyParams},
    BoxedUint, Integer, Inverter, Limb, Odd, PrecomputeInverter,
};
use num_bigint::BigUint;
use num_modular::ModularUnaryOps;
use proptest::prelude::*;
use std::cmp::Ordering;

fn retrieve_biguint(monty_form: &BoxedMontyForm) -> BigUint {
    to_biguint(&monty_form.retrieve())
}

fn reduce(n: &BoxedUint, p: BoxedMontyParams) -> BoxedMontyForm {
    let bits_precision = p.modulus().bits_precision();

    let n = match n.bits_precision().cmp(&bits_precision) {
        Ordering::Less => n.widen(bits_precision),
        Ordering::Equal => n.clone(),
        Ordering::Greater => n.shorten(bits_precision),
    };

    let n_reduced = n
        .rem_vartime(p.modulus().as_nz_ref())
        .widen(p.bits_precision());

    BoxedMontyForm::new(n_reduced, p)
}

prop_compose! {
    /// Generate a random `BoxedUint`.
    fn uint()(mut bytes in any::<Vec<u8>>()) -> BoxedUint {
        let extra = bytes.len() % Limb::BYTES;
        let bytes_precision = bytes.len() - extra;
        bytes.truncate(bytes_precision);
        BoxedUint::from_be_slice(&bytes, bytes_precision as u32 * 8).unwrap()
    }
}
prop_compose! {
    /// Generate a random odd modulus.
    fn modulus()(mut n in uint()) -> BoxedMontyParams {
        if n.is_even().into() {
            n = n.wrapping_add(&BoxedUint::one());
        }

        BoxedMontyParams::new(Odd::new(n).expect("modulus should be odd"))
    }
}
prop_compose! {
    /// Generate a single Montgomery form integer.
    fn monty_form()(a in uint(), n in modulus()) -> BoxedMontyForm {
        reduce(&a, n.clone())
    }
}
prop_compose! {
    /// Generate two Montgomery form integers with a common modulus.
    fn monty_form_pair()(a in uint(), b in uint(), n in modulus()) -> (BoxedMontyForm, BoxedMontyForm) {
        (reduce(&a, n.clone()), reduce(&b, n.clone()))
    }
}

proptest! {
    #[test]
    fn new(mut n in uint()) {
        if n.is_even().into() {
            n = n.wrapping_add(&BoxedUint::one());
        }

        let n = Odd::new(n).expect("ensured odd");
        let params1 = BoxedMontyParams::new(n.clone());
        let params2 = BoxedMontyParams::new_vartime(n);
        prop_assert_eq!(params1, params2);
    }

    #[test]
    fn inv(x in uint(), n in modulus()) {
        let x = reduce(&x, n.clone());
        let actual = Option::<BoxedMontyForm>::from(x.invert()).map(|a| a.retrieve());

        let x_bi = retrieve_biguint(&x);
        let n_bi = to_biguint(n.modulus());
        let expected = x_bi.invm(&n_bi);

        match (expected, actual) {
            (Some(exp), Some(act)) => prop_assert_eq!(exp, to_biguint(&act)),
            (None, None) => (),
            (_, _) => panic!("disagreement on if modular inverse exists")
        }
    }

    #[test]
    fn precomputed_inv(x in uint(), n in modulus()) {
        let x = reduce(&x, n.clone());
        let inverter = x.params().precompute_inverter();
        let actual = Option::<BoxedMontyForm>::from(inverter.invert(&x));

        let x_bi = retrieve_biguint(&x);
        let n_bi = to_biguint(n.modulus());
        let expected = x_bi.invm(&n_bi);

        match (expected, actual) {
            (Some(exp), Some(act)) => {
                prop_assert_eq!(exp, retrieve_biguint(&act));
            }
            (None, None) => (),
            (_, _) => panic!("disagreement on if modular inverse exists")
        }
    }

    #[test]
    fn mul((a, b) in monty_form_pair()) {
        let p = a.params().modulus();
        let actual = &a * &b;
        prop_assert!(actual.as_montgomery() < a.params().modulus());

        let a_bi = retrieve_biguint(&a);
        let b_bi = retrieve_biguint(&b);
        let p_bi = to_biguint(&p);
        let expected = (a_bi * b_bi) % p_bi;

        prop_assert_eq!(retrieve_biguint(&actual), expected);
    }

    #[test]
    fn square(a in monty_form()) {
        let p = a.params().modulus();
        let actual = a.square();
        prop_assert!(actual.as_montgomery() < a.params().modulus());

        let a_bi = retrieve_biguint(&a);
        let p_bi = to_biguint(&p);
        let expected = (&a_bi * &a_bi) % p_bi;

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
