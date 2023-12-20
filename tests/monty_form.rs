//! Equivalence tests between `crypto_bigint::MontyForm` and `num-bigint`.

use crypto_bigint::{Encoding, Integer, Invert, Inverter, NonZero, PrecomputeInverter, U256};
use num_bigint::{BigUint, ModInverse};
use proptest::prelude::*;

type MontyForm = crypto_bigint::modular::MontyForm<{ U256::LIMBS }>;
type MontyParams = crypto_bigint::modular::MontyParams<{ U256::LIMBS }>;

fn to_biguint(uint: &U256) -> BigUint {
    BigUint::from_bytes_le(uint.to_le_bytes().as_ref())
}

fn retrieve_biguint(monty_form: &MontyForm) -> BigUint {
    to_biguint(&monty_form.retrieve())
}

fn reduce(n: &U256, p: MontyParams) -> MontyForm {
    let modulus = NonZero::new(p.modulus().clone()).unwrap();
    let n_reduced = n.rem_vartime(&modulus);
    MontyForm::new(&n_reduced, p)
}

prop_compose! {
    fn uint()(bytes in any::<[u8; 32]>()) -> U256 {
        U256::from_le_slice(&bytes)
    }
}
prop_compose! {
    /// Generate a random odd modulus.
    fn modulus()(mut n in uint()) -> MontyParams {
        if n.is_even().into() {
            n = n.wrapping_add(&U256::one());
        }

        MontyParams::new(&n).expect("modulus should be valid")
    }
}

proptest! {
    #[test]
    fn inv(x in uint(), n in modulus()) {
        let x = reduce(&x, n.clone());
        let actual = Option::<MontyForm>::from(x.invert());

        let x_bi = retrieve_biguint(&x);
        let n_bi = to_biguint(n.modulus());
        let expected = x_bi.mod_inverse(&n_bi);

        match (expected, actual) {
            (Some(exp), Some(act)) => {
                let res = x * act;
                prop_assert_eq!(res.retrieve(), U256::ONE);
                prop_assert_eq!(exp, retrieve_biguint(&act).into());
            }
            (None, None) => (),
            (_, _) => panic!("disagreement on if modular inverse exists")
        }
    }

    #[test]
    fn precomputed_inv(x in uint(), n in modulus()) {
        let x = reduce(&x, n.clone());
        let inverter = x.params().precompute_inverter();
        let actual = Option::<MontyForm>::from(inverter.invert(&x));

        let x_bi = retrieve_biguint(&x);
        let n_bi = to_biguint(n.modulus());
        let expected = x_bi.mod_inverse(&n_bi);

        match (expected, actual) {
            (Some(exp), Some(act)) => {
                let res = x * act;
                prop_assert_eq!(res.retrieve(), U256::ONE);
                prop_assert_eq!(exp, retrieve_biguint(&act).into());
            }
            (None, None) => (),
            (_, _) => panic!("disagreement on if modular inverse exists")
        }
    }
}
