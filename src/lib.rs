#![no_std]
#![cfg_attr(docsrs, feature(doc_auto_cfg))]
#![doc = include_str!("../README.md")]
#![doc(
    html_logo_url = "https://raw.githubusercontent.com/RustCrypto/meta/master/logo.svg",
    html_favicon_url = "https://raw.githubusercontent.com/RustCrypto/meta/master/logo.svg"
)]
#![deny(unsafe_code)]
#![warn(
    clippy::mod_module_files,
    clippy::unwrap_used,
    missing_docs,
    missing_debug_implementations,
    missing_copy_implementations,
    rust_2018_idioms,
    trivial_casts,
    trivial_numeric_casts,
    unused_qualifications
)]

//! ## Usage
//!
//! The core types of `crypto-bigint` are as follows:
//!
//! - [`Uint`]: stack-allocated big integer type, const generic around a number of [`Limb`]s.
//!   Type aliases are provided for various sizes, e.g. [`U128`], [`U384`], [`U256`], [`U2048`],
//!   [`U3072`], [`U4096`].
//! - [`BoxedUint`]: heap-allocated big integer type. Requires the `alloc` crate feature is enabled.
//!
//! Big integer types in this crate use a 32-bit or 64-bit saturated representation, depending on
//! the underlying CPU's pointer width.
//!
//! The following types for modular arithmetic are available under the [`modular`] submodule:
//!
//! - [`modular::ConstMontyForm`]: stack-allocated type-safe modular arithmetic using Montgomery
//!   form suitable for cases where the modulus is known at compile-time.
//! - [`modular::MontyForm`]: stack-allocated modular arithmetic using Montgomery form for cases
//!   where the modulus is only known at runtime.
//! - [`modular::BoxedMontyForm`]: heap-allocated modular arithmetic using Montgomery form.
//!   Requires the `alloc` crate feature is enabled.
//!
//! ### `const fn` usage
//!
//! The [`Uint`] type provides a number of `const fn` inherent methods which
//! can be used for initializing and performing arithmetic on big integers in
//! const contexts:
//!
//! ```
//! use crypto_bigint::U256;
//!
//! // Parse a constant from a big endian hexadecimal string.
//! pub const MODULUS: U256 =
//!     U256::from_be_hex("ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551");
//!
//! // Compute `MODULUS` shifted right by 1 at compile time
//! pub const MODULUS_SHR1: U256 = MODULUS.shr(1);
//! ```
//!
//! ### Trait-based usage
//!
//! The [`Uint`] type itself does not implement the standard arithmetic traits
//! such as [`Add`], [`Sub`], [`Mul`], and [`Div`].
//!
//! To use these traits you must first pick a wrapper type which determines
//! overflow behavior: [`Wrapping`] or [`Checked`].
//!
//! #### Wrapping arithmetic
//!
//! ```
//! use crypto_bigint::{U256, Wrapping};
//!
//! let a = Wrapping(U256::MAX);
//! let b = Wrapping(U256::ONE);
//! let c = a + b;
//!
//! // `MAX` + 1 wraps back around to zero
//! assert_eq!(c.0, U256::ZERO);
//! ```
//!
//! #### Checked arithmetic
//!
//! ```
//! use crypto_bigint::{U256, Checked};
//!
//! let a = Checked::new(U256::ONE);
//! let b = Checked::new(U256::from(2u8));
//! let c = a + b;
//! assert_eq!(c.0.unwrap(), U256::from(3u8))
//! ```
//!
//! ### Modular arithmetic
//!
//! This library has initial support for modular arithmetic in the form of the
//! [`AddMod`], [`SubMod`], [`NegMod`], and [`MulMod`] traits, as well as the
//! support for the [`Rem`] trait when used with a [`NonZero`] operand.
//!
//! ```
//! use crypto_bigint::{AddMod, U256};
//!
//! // mod 3
//! let modulus = U256::from(3u8);
//!
//! // 1 + 1 mod 3 = 2
//! let a = U256::ONE.add_mod(&U256::ONE, &modulus);
//! assert_eq!(a, U256::from(2u8));
//!
//! // 2 + 1 mod 3 = 0
//! let b = a.add_mod(&U256::ONE, &modulus);
//! assert_eq!(b, U256::ZERO);
//! ```
//!
//! It also supports modular arithmetic over constant moduli using `ConstMontyForm`,
//! and over moduli set at runtime using `MontyForm`.
//! That includes modular exponentiation and multiplicative inverses.
//! These features are described in the [`modular`] module.
//!
//! ### Random number generation
//!
//! When the `rand_core` or `rand` features of this crate are enabled, it's
//! possible to generate random numbers using any CSRNG by using the
//! [`Random`] trait:
//!
//! ```
//! # #[cfg(feature = "rand")]
//! # {
//! use crypto_bigint::{Random, U256, rand_core::OsRng};
//!
//! let n = U256::random(&mut OsRng);
//! # }
//! ```
//!
//! #### Modular random number generation
//!
//! The [`RandomMod`] trait supports generating random numbers with a uniform
//! distribution around a given [`NonZero`] modulus.
//!
//! ```
//! # #[cfg(feature = "rand")]
//! # {
//! use crypto_bigint::{NonZero, RandomMod, U256, rand_core::OsRng};
//!
//! let modulus = NonZero::new(U256::from(3u8)).unwrap();
//! let n = U256::random_mod(&mut OsRng, &modulus);
//! # }
//! ```
//!
//! [`Add`]: core::ops::Add
//! [`Div`]: core::ops::Div
//! [`Mul`]: core::ops::Mul
//! [`Rem`]: core::ops::Rem
//! [`Sub`]: core::ops::Sub

#[cfg(feature = "alloc")]
#[allow(unused_imports)]
#[macro_use]
extern crate alloc;

#[macro_use]
mod macros;

pub mod modular;

#[cfg(feature = "hybrid-array")]
mod array;
mod checked;
mod const_choice;
mod limb;
mod non_zero;
mod odd;
mod primitives;
mod traits;
mod uint;
mod wrapping;

pub use crate::{
    checked::Checked,
    const_choice::{ConstChoice, ConstCtOption},
    limb::{Limb, WideWord, Word},
    non_zero::NonZero,
    odd::Odd,
    traits::*,
    uint::div_limb::Reciprocal,
    uint::*,
    wrapping::Wrapping,
};
pub use subtle;

#[cfg(feature = "alloc")]
pub use crate::uint::boxed::BoxedUint;

#[cfg(feature = "hybrid-array")]
pub use {
    crate::array::{ArrayDecoding, ArrayEncoding, ByteArray},
    hybrid_array::{self, typenum::consts},
};

#[cfg(feature = "rand_core")]
pub use rand_core;

#[cfg(feature = "rlp")]
pub use rlp;

#[cfg(feature = "zeroize")]
pub use zeroize;

/// Import prelude for this crate: includes important traits.
pub mod prelude {
    pub use crate::traits::*;

    #[cfg(feature = "hybrid-array")]
    pub use crate::array::{ArrayDecoding, ArrayEncoding};
}
