//! Equivalence tests between `crypto_bigint::Uint` and `num_bigint::BigUint`.

mod common;

use common::to_biguint;
use crypto_bigint::{
    modular::{MontyForm, MontyParams},
    Encoding, Limb, NonZero, Odd, Word, U256,
};
use num_bigint::BigUint;
use num_integer::Integer as _;
use num_traits::identities::{One, Zero};
use proptest::prelude::*;
use std::mem;

/// Example prime number (NIST P-256 curve order)
const P: Odd<U256> =
    Odd::<U256>::from_be_hex("ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551");

fn to_uint(big_uint: BigUint) -> U256 {
    let mut input = [0u8; U256::BYTES];
    let encoded = big_uint.to_bytes_le();
    let l = encoded.len().min(U256::BYTES);
    input[..l].copy_from_slice(&encoded[..l]);

    U256::from_le_slice(&input)
}

prop_compose! {
    fn uint()(bytes in any::<[u8; 32]>()) -> U256 {
        U256::from_le_slice(&bytes)
    }
}
prop_compose! {
    fn uint_mod_p(p: Odd<U256>)(a in uint()) -> U256 {
        a.wrapping_rem_vartime(&p)
    }
}
prop_compose! {
    fn nonzero_limb()(x in any::<Word>()) -> Limb {
        if x == 0 { Limb::from(1u32) } else {Limb::from(x)}
    }
}

proptest! {
    #[test]
    fn roundtrip(a in uint()) {
        assert_eq!(a, to_uint(to_biguint(&a)));
    }

    #[test]
    fn bits(a in uint()) {
        let expected = to_biguint(&a).bits() as u32;
        assert_eq!(expected, a.bits());
        assert_eq!(expected, a.bits_vartime());
    }

    #[test]
    fn shl_vartime(a in uint(), shift in any::<u8>()) {
        let a_bi = to_biguint(&a);

        // Add a 50% probability of overflow.
        let shift = u32::from(shift) % (U256::BITS * 2);

        let expected = to_uint(a_bi << shift as usize);
        let actual = a.overflowing_shl_vartime(shift.into());

        if shift >= U256::BITS {
            assert!(bool::from(actual.is_none()));
        }
        else {
            assert_eq!(expected, actual.unwrap());
        }
    }

    #[test]
    fn shl(a in uint(), shift in any::<u16>()) {
        let a_bi = to_biguint(&a);

        // Add a 50% probability of overflow.
        let shift = u32::from(shift) % (U256::BITS * 2);

        let expected = to_uint(a_bi << shift as usize);
        let actual = a.overflowing_shl(shift);

        if shift >= U256::BITS {
            assert!(bool::from(actual.is_none()));
        }
        else {
            assert_eq!(expected, actual.unwrap());
        }
    }

    #[test]
    fn shr_vartime(a in uint(), shift in any::<u16>()) {
        let a_bi = to_biguint(&a);

        // Add a 50% probability of overflow.
        let shift = u32::from(shift) % (U256::BITS * 2);

        let expected = to_uint(a_bi >> shift as usize);
        let actual = a.overflowing_shr_vartime(shift);

        if shift >= U256::BITS {
            assert!(bool::from(actual.is_none()));
        }
        else {
            assert_eq!(expected, actual.unwrap());
        }
    }

    #[test]
    fn shr(a in uint(), shift in any::<u16>()) {
        let a_bi = to_biguint(&a);

        // Add a 50% probability of overflow.
        let shift = u32::from(shift) % (U256::BITS * 2);

        let expected = to_uint(a_bi >> shift as usize);
        let actual = a.overflowing_shr(shift);

        if shift >= U256::BITS {
            assert!(bool::from(actual.is_none()));
        }
        else {
            assert_eq!(expected, actual.unwrap());
        }
    }

    #[test]
    fn wrapping_add(a in uint(), b in uint()) {
        let a_bi = to_biguint(&a);
        let b_bi = to_biguint(&b);

        let expected = to_uint(a_bi + b_bi);
        let actual = a.wrapping_add(&b);

        assert_eq!(expected, actual);
    }

    #[test]
    fn add_mod_nist_p256(a in uint_mod_p(P), b in uint_mod_p(P)) {
        assert!(a < P);
        assert!(b < P);

        let a_bi = to_biguint(&a);
        let b_bi = to_biguint(&b);
        let p_bi = to_biguint(&P);

        let expected = to_uint((a_bi + b_bi) % p_bi);
        let actual = a.add_mod(&b, &P);

        assert!(expected < P);
        assert!(actual < P);

        assert_eq!(expected, actual);
    }

    #[test]
    fn sub_mod_nist_p256(mut a in uint_mod_p(P), mut b in uint_mod_p(P)) {
        if b > a {
            mem::swap(&mut a, &mut b);
        }

        assert!(a < P);
        assert!(b < P);

        let a_bi = to_biguint(&a);
        let b_bi = to_biguint(&b);
        let p_bi = to_biguint(&P);

        let expected = to_uint((a_bi - b_bi) % p_bi);
        let actual = a.sub_mod(&b, &P);

        assert!(expected < P);
        assert!(actual < P);

        assert_eq!(expected, actual);
    }

    #[test]
    fn mul_mod_nist_p256(a in uint_mod_p(P), b in uint_mod_p(P)) {
        assert!(a < P);
        assert!(b < P);

        let a_bi = to_biguint(&a);
        let b_bi = to_biguint(&b);
        let p_bi = to_biguint(&P);

        let expected = to_uint((a_bi * b_bi) % p_bi);
        let actual = a.mul_mod_vartime(&b, &P);

        assert!(expected < P);
        assert!(actual < P);

        assert_eq!(expected, actual);
    }

    #[test]
    fn wrapping_sub(mut a in uint(), mut b in uint()) {
        if b > a {
            mem::swap(&mut a, &mut b);
        }

        let a_bi = to_biguint(&a);
        let b_bi = to_biguint(&b);

        let expected = to_uint(a_bi - b_bi);
        let actual = a.wrapping_sub(&b);

        assert_eq!(expected, actual);
    }

    #[test]
    fn wrapping_mul(a in uint(), b in uint()) {
        let a_bi = to_biguint(&a);
        let b_bi = to_biguint(&b);

        let expected = to_uint(a_bi * b_bi);
        let actual = a.wrapping_mul(&b);

        assert_eq!(expected, actual);
    }

    #[test]
    fn wrapping_div(a in uint(), b in uint()) {
        let a_bi = to_biguint(&a);
        let b_bi = to_biguint(&b);

        if !b_bi.is_zero() {
            let expected = to_uint(a_bi / b_bi);
            let b_nz = NonZero::new(b).unwrap();
            let actual = a.wrapping_div(&b_nz);
            assert_eq!(expected, actual);
            let actual_vartime = a.wrapping_div_vartime(&b_nz);
            assert_eq!(expected, actual_vartime);
        }
    }

    #[test]
    fn wrapping_rem(a in uint(), b in uint()) {
        let a_bi = to_biguint(&a);
        let b_bi = to_biguint(&b);

        if !b_bi.is_zero() {
            let expected = to_uint(a_bi % b_bi);
            let actual = a.wrapping_rem_vartime(&b);

            assert_eq!(expected, actual);
        }
    }

    #[test]
    fn div_rem_limb(a in uint(), b in nonzero_limb()) {
        let a_bi = to_biguint(&a);
        let b_bi = to_biguint(&U256::from(b));

        let (expected_quo, expected_rem) = a_bi.div_rem(&b_bi);
        let (actual_quo, actual_rem) = a.div_rem_limb(NonZero::new(b).unwrap());
        assert_eq!(to_uint(expected_quo), actual_quo);
        assert_eq!(to_uint(expected_rem), U256::from(actual_rem));
    }

    #[test]
    fn div_rem_limb_min_max(a in uint()) {
        let a_bi = to_biguint(&a);

        for b in [Limb::from(1u32), Limb::MAX] {
            let b_bi = to_biguint(&U256::from(b));
            let (expected_quo, expected_rem) = a_bi.div_rem(&b_bi);
            let (actual_quo, actual_rem) = a.div_rem_limb(NonZero::new(b).unwrap());
            assert_eq!(to_uint(expected_quo), actual_quo);
            assert_eq!(to_uint(expected_rem), U256::from(actual_rem));
        }
    }

    #[test]
    fn gcd(f in uint(), g in uint()) {
        let f_bi = to_biguint(&f);
        let g_bi = to_biguint(&g);

        let expected = to_uint(f_bi.gcd(&g_bi));
        let actual = f.gcd(&g);
        assert_eq!(expected, actual);
    }

    #[test]
    fn inv_mod2k(a in uint(), k in any::<u32>()) {
        let a = a | U256::ONE; // make odd
        let k = k % (U256::BITS + 1);
        let a_bi = to_biguint(&a);
        let m_bi = BigUint::one() << k as usize;

        let actual = a.inv_mod2k(k).unwrap();
        let actual_vartime = a.inv_mod2k_vartime(k).unwrap();
        assert_eq!(actual, actual_vartime);

        if k == 0 {
            assert_eq!(actual, U256::ZERO);
        }
        else {
            let inv_bi = to_biguint(&actual);
            let res = (inv_bi * a_bi) % m_bi;
            assert_eq!(res, BigUint::one());
        }
    }

    #[test]
    fn inv_mod(a in uint(), b in uint()) {
        let a_bi = to_biguint(&a);
        let b_bi = to_biguint(&b);

        let expected_is_some = a_bi.gcd(&b_bi) == BigUint::one();
        let actual = a.inv_mod(&b);
        let actual_is_some = bool::from(actual.is_some());

        assert_eq!(expected_is_some, actual_is_some);

        if actual_is_some {
            let actual = actual.unwrap();
            let inv_bi = to_biguint(&actual);
            let res = (inv_bi * a_bi) % b_bi;
            assert_eq!(res, BigUint::one());
        }
    }

    #[test]
    fn wrapping_sqrt(a in uint()) {
        let a_bi = to_biguint(&a);
        let expected = to_uint(a_bi.sqrt());
        let actual_ct = a.wrapping_sqrt();
        assert_eq!(expected, actual_ct);

        let actual_vartime = a.wrapping_sqrt_vartime();
        assert_eq!(expected, actual_vartime);
    }

    #[test]
    fn wrapping_or(a in uint(), b in uint()) {
        let a_bi = to_biguint(&a);
        let b_bi = to_biguint(&b);

        let expected = to_uint(a_bi | b_bi);
        let actual = a.wrapping_or(&b);
        assert_eq!(expected, actual);
    }

    #[test]
    fn wrapping_and(a in uint(), b in uint()) {
        let a_bi = to_biguint(&a);
        let b_bi = to_biguint(&b);

        let expected = to_uint(a_bi & b_bi);
        let actual = a.wrapping_and(&b);
        assert_eq!(expected, actual);
    }

    #[test]
    fn wrapping_xor(a in uint(), b in uint()) {
        let a_bi = to_biguint(&a);
        let b_bi = to_biguint(&b);

        let expected = to_uint(a_bi ^ b_bi);
        let actual = a.wrapping_xor(&b);
        assert_eq!(expected, actual);
    }

    #[test]
    fn wrapping_shl(n in uint(), shift in any::<u32>()) {
        let n_bi = to_biguint(&n);

        let expected = if shift < U256::BITS {
            to_uint(n_bi << shift)
        } else {
            U256::ZERO
        };

        let actual_ct = n.wrapping_shl(shift);
        assert_eq!(expected, actual_ct);

        let actual_vartime = n.wrapping_shl_vartime(shift);
        assert_eq!(expected, actual_vartime);
    }

    #[test]
    fn wrapping_shr(n in uint(), shift in any::<u32>()) {
        let n_bi = to_biguint(&n);
        let expected = to_uint(n_bi >> shift);

        let actual_ct = n.wrapping_shr(shift);
        assert_eq!(expected, actual_ct);

        let actual_vartime = n.wrapping_shr_vartime(shift);
        assert_eq!(expected, actual_vartime);
    }

    #[test]
    fn encoding(a in uint()) {
        assert_eq!(a, U256::from_be_bytes(a.to_be_bytes()));
        assert_eq!(a, U256::from_le_bytes(a.to_le_bytes()));
    }

    #[test]
    fn encoding_reverse(a in uint()) {
        let mut bytes = a.to_be_bytes();
        bytes.reverse();
        assert_eq!(a, U256::from_le_bytes(bytes));

        let mut bytes = a.to_le_bytes();
        bytes.reverse();
        assert_eq!(a, U256::from_be_bytes(bytes));
    }

    #[test]
    fn monty_form_pow(a in uint_mod_p(P), b in uint()) {
        let a_bi = to_biguint(&a);
        let b_bi = to_biguint(&b);
        let p_bi = to_biguint(&P);

        let expected = to_uint(a_bi.modpow(&b_bi, &p_bi));
        let params = MontyParams::new_vartime(P);
        let a_m = MontyForm::new(&a, params);
        let actual = a_m.pow(&b).retrieve();

        assert_eq!(expected, actual);
    }

    #[test]
    fn monty_form_pow_bounded_exp(a in uint_mod_p(P), b in uint(), exponent_bits in any::<u8>()) {
        let b_masked = b & (U256::ONE << exponent_bits as u32).wrapping_sub(&U256::ONE);

        let a_bi = to_biguint(&a);
        let b_bi = to_biguint(&b_masked);
        let p_bi = to_biguint(&P);

        let expected = to_uint(a_bi.modpow(&b_bi, &p_bi));

        let params = MontyParams::new_vartime(P);
        let a_m = MontyForm::new(&a, params);
        let actual = a_m.pow_bounded_exp(&b, exponent_bits.into()).retrieve();

        assert_eq!(expected, actual);
    }

    #[test]
    fn monty_form_div_by_2(a in uint_mod_p(P)) {
        let a_bi = to_biguint(&a);
        let p_bi = to_biguint(&P);
        let two = BigUint::from(2u32);

        let expected = if a_bi.is_even() {
            &a_bi / two
        }
        else {
            (&a_bi + &p_bi) / two
        };
        let expected = to_uint(expected);

        let params = MontyParams::new_vartime(P);
        let a_m = MontyForm::new(&a, params);
        let actual = a_m.div_by_2().retrieve();

        assert_eq!(expected, actual);
    }
}
