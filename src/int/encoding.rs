//! Const-friendly decoding/encoding operations for [`Int`].

use crate::{Int, Uint};

impl<const LIMBS: usize> Int<LIMBS> {
    pub const fn from_be_hex(hex: &str) -> Self {
        Self(Uint::from_be_hex(hex))
    }
}
