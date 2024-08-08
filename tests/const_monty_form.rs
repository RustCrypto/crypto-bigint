//! Equivalence tests between `crypto_bigint::ConstMontyForm` and `num-bigint`.

mod common;

use common::to_biguint;
use crypto_bigint::{impl_modulus, modular::ConstMontyParams, Invert, Inverter, U256};
use num_bigint::BigUint;
use num_modular::ModularUnaryOps;
use proptest::prelude::*;

impl_modulus!(
    Modulus,
    U256,
    "ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551"
);

type ConstMontyForm = crypto_bigint::modular::ConstMontyForm<Modulus, { U256::LIMBS }>;

fn retrieve_biguint(monty_form: &ConstMontyForm) -> BigUint {
    to_biguint(&monty_form.retrieve())
}

fn reduce(n: &U256) -> ConstMontyForm {
    ConstMontyForm::new(n)
}

prop_compose! {
    fn uint()(bytes in any::<[u8; 32]>()) -> U256 {
        U256::from_le_slice(&bytes)
    }
}

proptest! {
    #[test]
    fn inv(x in uint()) {
        let x = reduce(&x);
        let actual = Option::<ConstMontyForm>::from(x.invert());

        let x_bi = retrieve_biguint(&x);
        let n_bi = to_biguint(&Modulus::MODULUS);
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
    fn precomputed_inv(x in uint()) {
        let x = reduce(&x);
        let inverter = Modulus::precompute_inverter();
        let actual = Option::<ConstMontyForm>::from(inverter.invert(&x));

        let x_bi = retrieve_biguint(&x);
        let n_bi = to_biguint(&Modulus::MODULUS);
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
}
