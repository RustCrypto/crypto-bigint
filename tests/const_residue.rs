//! Test to ensure that `const_residue!` works from outside this crate.

use crypto_bigint::{impl_modulus, const_residue, U64, modular::constant_mod::ResidueParams};

impl_modulus!(TestMod, U64, "30e4b8f030ab42f3");

fn _test_fun() {
    let base = U64::from(2u64);
    let _base_mod = const_residue!(base, TestMod);
}
