//! Equivalence tests for Bernstein-Yang inversions.

use crypto_bigint::{modular::BernsteinYangInverter, Encoding, U256};
use num_bigint::BigUint;
use num_integer::Integer;
use num_traits::One;
use proptest::prelude::*;

/// Example prime number (NIST P-256 curve order)
const P: U256 =
    U256::from_be_hex("ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551");

fn to_biguint(uint: &U256) -> BigUint {
    BigUint::from_bytes_le(uint.to_le_bytes().as_ref())
}

prop_compose! {
    fn uint()(bytes in any::<[u8; 32]>()) -> U256 {
        U256::from_le_slice(&bytes)
    }
}
prop_compose! {
    fn uint_mod_p(p: U256)(a in uint()) -> U256 {
        a.wrapping_rem(&p)
    }
}

proptest! {
    #[test]
    fn inv_mod(x in uint()) {
        let x_bi = to_biguint(&x);
        let p_bi = to_biguint(&P);

        let expected_is_some = x_bi.gcd(&p_bi) == BigUint::one();

        let inverter = BernsteinYangInverter::<6>::new(P.as_words(), &[1]);
        let actual = inverter.invert::<{U256::LIMBS}>(x.as_words());

        prop_assert_eq!(bool::from(expected_is_some), actual.is_some());

        if let Some(actual) = actual {
            let inv_bi = to_biguint(&U256::from(actual));
            let res = (inv_bi * x_bi) % p_bi;
            prop_assert_eq!(res, BigUint::one());
        }
    }
}
