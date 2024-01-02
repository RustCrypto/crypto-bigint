//! Common functionality shared between tests.

// Different tests may use only a subset of the available functionality
#![allow(dead_code)]

use crypto_bigint::{Encoding, Limb};
use num_bigint::BigUint;

/// `Uint` to `num_bigint::BigUint`
pub fn to_biguint<T>(uint: &T) -> BigUint
where
    T: AsRef<[Limb]>,
{
    let mut bytes = Vec::with_capacity(uint.as_ref().len() * Limb::BYTES);

    for limb in uint.as_ref() {
        bytes.extend_from_slice(&limb.to_le_bytes());
    }

    BigUint::from_bytes_le(&bytes)
}
