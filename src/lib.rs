//! Pure Rust implementation of a big integer library designed for cryptography.
//!
//! # About
//! This library has been designed  from the ground-up for use in cryptographic
//! applications. It provides constant-time, `no_std`-friendly implementations
//! of modern formulas implemented using const generics.
//!
//! # Minimum Supported Rust Version
//! **Rust 1.56** at a minimum.
//!
//! # Goals
//! - No heap allocations i.e. `no_std`-friendly.
//! - Constant-time by default using traits from the [`subtle`] crate.
//! - Leverage what is possible today with const generics on `stable` rust.
//! - Support `const fn` as much as possible, including decoding big integers from
//!   bytes/hex and performing arithmetic operations on them, with the goal of
//!   being able to compute values at compile-time.
//!
//! # Status
//! This library presently provides only a baseline level of functionality.
//! It's new, unaudited, and may contain bugs. We recommend that it only be
//! used in an experimental capacity for now.
//!
//! Please see the [feature wishlist tracking ticket] for more information.
//!
//! [feature wishlist tracking ticket]: https://github.com/RustCrypto/crypto-bigint/issues/1

#![no_std]
#![cfg_attr(docsrs, feature(doc_cfg))]
#![doc(
    html_logo_url = "https://raw.githubusercontent.com/RustCrypto/meta/master/logo.svg",
    html_favicon_url = "https://raw.githubusercontent.com/RustCrypto/meta/master/logo.svg",
    html_root_url = "https://docs.rs/crypto-bigint/0.3.0-pre"
)]
#![forbid(unsafe_code, clippy::unwrap_used)]
#![warn(
    missing_docs,
    missing_debug_implementations,
    missing_copy_implementations,
    rust_2018_idioms,
    trivial_casts,
    trivial_numeric_casts,
    unused_qualifications
)]

#[cfg(all(feature = "alloc", test))]
extern crate alloc;

#[macro_use]
mod macros;

#[cfg(feature = "generic-array")]
mod array;
mod checked;
mod limb;
mod non_zero;
mod traits;
mod uint;
mod wrapping;

pub use crate::{
    checked::Checked,
    limb::{Limb, LimbUInt, WideLimbUInt},
    non_zero::NonZero,
    traits::*,
    uint::*,
    wrapping::Wrapping,
};
pub use subtle;

pub(crate) use limb::{LimbInt, WideLimbInt};

#[cfg(feature = "generic-array")]
pub use {
    self::array::{ArrayDecoding, ArrayEncoding, ByteArray},
    generic_array::{self, typenum::consts},
};

#[cfg(feature = "rlp")]
pub use rlp;

#[cfg(feature = "zeroize")]
pub use zeroize;
