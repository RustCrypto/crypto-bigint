//! Equivalence tests between `crypto_bigint::BoxedUint` and `num_bigint::BigUint`.

#![cfg(feature = "alloc")]

mod common;

use common::to_biguint;
use core::cmp::Ordering;
use crypto_bigint::{BoxedUint, CheckedAdd, Gcd, Integer, Limb, NonZero};
use num_bigint::BigUint;
use num_integer::Integer as _;
use num_modular::ModularUnaryOps;
use num_traits::identities::One;
use proptest::prelude::*;

fn to_uint(big_uint: BigUint) -> BoxedUint {
    let bytes = big_uint.to_bytes_be();
    let pad_count = Limb::BYTES - (bytes.len() % Limb::BYTES);
    let mut padded_bytes = vec![0u8; pad_count];
    padded_bytes.extend_from_slice(&bytes);
    BoxedUint::from_be_slice(&padded_bytes, padded_bytes.len() as u32 * 8).unwrap()
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
        BoxedUint::from_be_slice(&bytes, bytes_precision as u32 * 8).unwrap()
    }
}
prop_compose! {
    /// Generate a pair of random `BoxedUint`s with the same precision.
    fn uint_pair()(mut a in uint(), mut b in uint()) -> (BoxedUint, BoxedUint) {
        match a.bits_precision().cmp(&b.bits_precision()) {
            Ordering::Greater => {
                b = b.widen(a.bits_precision());
            }
            Ordering::Less => {
                a = a.widen(b.bits_precision());
            },
            _ => ()
        };
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
    fn bits(a in uint()) {
        let expected = to_biguint(&a).bits() as u32;
        prop_assert_eq!(expected, a.bits());
        prop_assert_eq!(expected, a.bits_vartime());
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
    fn checked_div((a, b) in uint_pair()) {
        let actual = a.checked_div(&b);

        if b.is_zero().into() {
            prop_assert!(bool::from(actual.is_none()));
        } else {
            let a_bi = to_biguint(&a);
            let b_bi = to_biguint(&b);
            let expected = &a_bi / &b_bi;
            prop_assert_eq!(expected, to_biguint(&actual.unwrap()));
        }
    }

    #[test]
    fn div_rem((a, mut b) in uint_pair()) {
        if b.is_zero().into() {
            b = b.wrapping_add(&BoxedUint::one());
        }

        let a_bi = to_biguint(&a);
        let b_bi = to_biguint(&b);
        let expected_quotient = &a_bi / &b_bi;
        let expected_remainder = a_bi % b_bi;

        let (actual_quotient, actual_remainder) = a.div_rem(&NonZero::new(b).unwrap());
        prop_assert_eq!(expected_quotient, to_biguint(&actual_quotient));
        prop_assert_eq!(expected_remainder, to_biguint(&actual_remainder));
    }

    #[test]
    fn div_rem_vartime((a, mut b) in uint_pair()) {
        if b.is_zero().into() {
            b = b.wrapping_add(&BoxedUint::one());
        }

        let a_bi = to_biguint(&a);
        let b_bi = to_biguint(&b);
        let expected_quotient = &a_bi / &b_bi;
        let expected_remainder = a_bi % b_bi;

        let (actual_quotient, actual_remainder) = a.div_rem_vartime(&NonZero::new(b).unwrap());
        prop_assert_eq!(expected_quotient, to_biguint(&actual_quotient));
        prop_assert_eq!(expected_remainder, to_biguint(&actual_remainder));
    }

    #[test]
    fn gcd((f, g) in uint_pair()) {
        let f_bi = to_biguint(&f);
        let g_bi = to_biguint(&g);

        let expected = to_uint(f_bi.gcd(&g_bi));
        let actual = f.gcd(&g);
        prop_assert_eq!(expected, actual);
    }

    #[test]
    fn mod_inv((a, mut b) in uint_pair()) {
        if b.is_even().into() {
            b = BoxedUint::one_with_precision(a.bits_precision());
        }

        let b = b.to_odd().unwrap();

        let a_bi = to_biguint(&a);
        let b_bi = to_biguint(&b);
        let expected = a_bi.invm(&b_bi);
        let actual = Option::<BoxedUint>::from(a.inv_odd_mod(&b));

        match (expected, actual) {
            (Some(exp), Some(act)) => prop_assert_eq!(exp, to_biguint(&act)),
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
        prop_assert_eq!(expected, actual);
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
    fn rem((a, b) in uint_pair()) {
        if bool::from(!b.is_zero()) {
            let a_bi = to_biguint(&a);
            let b_bi = to_biguint(&b);

            let expected = a_bi % b_bi;
            let actual = a.rem(&NonZero::new(b).unwrap());

            prop_assert_eq!(expected, to_biguint(&actual));
        }
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

    #[test]
    fn shl(a in uint(), shift in any::<u16>()) {
        let a_bi = to_biguint(&a);

        // Add a 50% probability of overflow.
        let shift = u32::from(shift) % (a.bits_precision() * 2);

        let expected = to_uint((a_bi << shift as usize) & ((BigUint::one() << a.bits_precision() as usize) - BigUint::one()));
        let (actual, overflow) = a.overflowing_shl(shift);

        prop_assert_eq!(&expected, &actual);
        if shift >= a.bits_precision() {
            prop_assert_eq!(actual, BoxedUint::zero());
            prop_assert!(bool::from(overflow));
        }
    }

    #[test]
    fn shl_vartime(a in uint(), shift in any::<u16>()) {
        let a_bi = to_biguint(&a);

        // Add a 50% probability of overflow.
        let shift = u32::from(shift) % (a.bits_precision() * 2);

        let expected = to_uint((a_bi << shift as usize) & ((BigUint::one() << a.bits_precision() as usize) - BigUint::one()));
        let actual = a.shl_vartime(shift);

        if shift >= a.bits_precision() {
            prop_assert!(actual.is_none());
        }
        else {
            prop_assert_eq!(expected, actual.unwrap());
        }
    }

    #[test]
    fn shr(a in uint(), shift in any::<u16>()) {
        let a_bi = to_biguint(&a);

        // Add a 50% probability of overflow.
        let shift = u32::from(shift) % (a.bits_precision() * 2);

        let expected = to_uint(a_bi >> shift as usize);
        let (actual, overflow) = a.overflowing_shr(shift);

        prop_assert_eq!(&expected, &actual);
        if shift >= a.bits_precision() {
            prop_assert_eq!(actual, BoxedUint::zero());
            prop_assert!(bool::from(overflow));
        }
    }


    #[test]
    fn shr_vartime(a in uint(), shift in any::<u16>()) {
        let a_bi = to_biguint(&a);

        // Add a 50% probability of overflow.
        let shift = u32::from(shift) % (a.bits_precision() * 2);

        let expected = to_uint(a_bi >> shift as usize);
        let actual = a.shr_vartime(shift);

        if shift >= a.bits_precision() {
            prop_assert!(actual.is_none());
        }
        else {
            prop_assert_eq!(expected, actual.unwrap());
        }
    }


    #[test]
    fn radix_encode_vartime(a in uint(), radix in 2u32..=36) {
        let a_bi = to_biguint(&a);

        let expected_enc = a_bi.to_str_radix(radix);
        let actual_enc = a.to_string_radix_vartime(radix);
        prop_assert_eq!(&expected_enc, &actual_enc);

        let decoded = BoxedUint::from_str_radix_vartime(&actual_enc, radix).expect("decoding error");
        let dec_bi = to_biguint(&decoded);
        prop_assert_eq!(dec_bi, a_bi);

    }
}
