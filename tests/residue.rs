//! Equivalence tests between `crypto_bigint::Residue` and `num-bigint`.

use crypto_bigint::{impl_modulus, modular::ResidueParams, Encoding, Invert, Inverter, U256};
use num_bigint::{BigUint, ModInverse};
use proptest::prelude::*;

impl_modulus!(
    Modulus,
    U256,
    "ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551"
);

type Residue = crypto_bigint::modular::Residue<Modulus, { U256::LIMBS }>;

fn to_biguint(uint: &U256) -> BigUint {
    BigUint::from_bytes_le(uint.to_le_bytes().as_ref())
}

fn retrieve_biguint(residue: &Residue) -> BigUint {
    to_biguint(&residue.retrieve())
}

fn reduce(n: &U256) -> Residue {
    Residue::new(&n)
}

prop_compose! {
    fn uint()(bytes in any::<[u8; 32]>()) -> U256 {
        U256::from_le_slice(&bytes)
    }
}
prop_compose! {
    /// Generate a single residue.
    fn residue()(a in uint()) -> Residue {
        reduce(&a)
    }
}

proptest! {
    #[test]
    fn inv(x in uint()) {
        let x = reduce(&x);
        let actual = Option::<Residue>::from(x.invert());

        let x_bi = retrieve_biguint(&x);
        let n_bi = to_biguint(&Modulus::MODULUS);
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
    fn precomputed_inv(x in uint()) {
        let x = reduce(&x);
        let inverter = Modulus::precompute_inverter();
        let actual = Option::<Residue>::from(inverter.invert(&x));

        let x_bi = retrieve_biguint(&x);
        let n_bi = to_biguint(&Modulus::MODULUS);
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
