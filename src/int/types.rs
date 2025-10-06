//! Selection of [`Int`] types.
//! todo: replace with macro implementation once serde is set up.

use crate::Int;

#[cfg(any(target_pointer_width = "64", target_family = "wasm"))]
/// Signed bit integer.
pub type I64 = Int<1>;

#[cfg(any(target_pointer_width = "64", target_family = "wasm"))]
/// Signed bit integer.
pub type I128 = Int<2>;

#[cfg(any(target_pointer_width = "64", target_family = "wasm"))]
/// Signed bit integer.
pub type I256 = Int<4>;

#[cfg(any(target_pointer_width = "64", target_family = "wasm"))]
/// Signed bit integer.
pub type I512 = Int<8>;

#[cfg(any(target_pointer_width = "64", target_family = "wasm"))]
/// Signed bit integer.
pub type I1024 = Int<16>;

#[cfg(any(target_pointer_width = "64", target_family = "wasm"))]
/// Signed bit integer.
pub type I2048 = Int<32>;

#[cfg(any(target_pointer_width = "64", target_family = "wasm"))]
/// Signed bit integer.
pub type I4096 = Int<64>;

#[cfg(all(target_pointer_width = "32", not(target_family = "wasm")))]
/// Signed bit integer.
pub type I64 = Int<2>;

#[cfg(all(target_pointer_width = "32", not(target_family = "wasm")))]
/// Signed bit integer.
pub type I128 = Int<4>;

#[cfg(all(target_pointer_width = "32", not(target_family = "wasm")))]
/// Signed bit integer.
pub type I256 = Int<8>;

#[cfg(all(target_pointer_width = "32", not(target_family = "wasm")))]
/// Signed bit integer.
pub type I512 = Int<16>;

#[cfg(all(target_pointer_width = "32", not(target_family = "wasm")))]
/// Signed bit integer.
pub type I1024 = Int<32>;

#[cfg(all(target_pointer_width = "32", not(target_family = "wasm")))]
/// Signed bit integer.
pub type I2048 = Int<64>;

#[cfg(all(target_pointer_width = "32", not(target_family = "wasm")))]
/// Signed bit integer.
pub type I4096 = Int<128>;
