//! Equivalence tests between `crypto_bigint::MontyForm` and `num-bigint`.

mod common;

use common::to_biguint;
use crypto_bigint::{Integer, Invert, Inverter, Odd, PrecomputeInverter, U256};
use num_bigint::BigUint;
use num_modular::ModularUnaryOps;
use proptest::prelude::*;

type MontyForm = crypto_bigint::modular::MontyForm<{ U256::LIMBS }>;
type MontyParams = crypto_bigint::modular::MontyParams<{ U256::LIMBS }>;

fn retrieve_biguint(monty_form: &MontyForm) -> BigUint {
    to_biguint(&monty_form.retrieve())
}

fn reduce(n: &U256, p: MontyParams) -> MontyForm {
    let n_reduced = n.rem_vartime(p.modulus().as_nz_ref());
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

        MontyParams::new_vartime(Odd::new(n).expect("modulus ensured odd"))
    }
}

proptest! {
    #[test]
    fn new(n in modulus()) {
        let n2 = MontyParams::new(*n.modulus());
        prop_assert_eq!(n, n2);
    }

    #[test]
    fn inv(x in uint(), n in modulus()) {
        let x = reduce(&x, n);
        let actual = Option::<MontyForm>::from(x.invert());

        let x_bi = retrieve_biguint(&x);
        let n_bi = to_biguint(n.modulus());
        let expected = x_bi.invm(&n_bi);

        match (expected, actual) {
            (Some(exp), Some(act)) => {
                let res = x * act;
                prop_assert_eq!(res.retrieve(), U256::ONE);
                prop_assert_eq!(exp, retrieve_biguint(&act));
            }
            (None, None) => (),
            (_, _) => panic!("disagreement on if modular inverse exists")
        }
    }

    #[test]
    fn precomputed_inv(x in uint(), n in modulus()) {
        let x = reduce(&x, n);
        let inverter = x.params().precompute_inverter();
        let actual = Option::<MontyForm>::from(inverter.invert(&x));

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
}
