//! Test to ensure that `impl_modulus!` works from outside this crate.

use crypto_bigint::{U64, impl_modulus};

impl_modulus!(TestMod, U64, "30e4b8f030ab42f3");
