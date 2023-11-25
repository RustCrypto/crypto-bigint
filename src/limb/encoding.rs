//! Limb encoding

use super::{Limb, Word};
use crate::Encoding;

impl Encoding for Limb {
    #[cfg(target_pointer_width = "32")]
    type Repr = [u8; 4];
    #[cfg(target_pointer_width = "64")]
    type Repr = [u8; 8];

    #[inline]
    fn from_be_bytes(bytes: Self::Repr) -> Self {
        Limb(Word::from_be_bytes(bytes))
    }

    #[inline]
    fn from_le_bytes(bytes: Self::Repr) -> Self {
        Limb(Word::from_le_bytes(bytes))
    }

    #[inline]
    fn to_be_bytes(&self) -> Self::Repr {
        self.0.to_be_bytes()
    }

    #[inline]
    fn to_le_bytes(&self) -> Self::Repr {
        self.0.to_le_bytes()
    }
}

#[cfg(feature = "alloc")]
impl Limb {
    /// Decode limb from a big endian byte slice.
    ///
    /// Panics if the slice is not the same size as [`Limb::Repr`].
    pub(crate) fn from_be_slice(bytes: &[u8]) -> Self {
        Self::from_be_bytes(bytes.try_into().expect("slice not limb-sized"))
    }

    /// Decode limb from a little endian byte slice.
    ///
    /// Panics if the slice is not the same size as [`Limb::Repr`].
    pub(crate) fn from_le_slice(bytes: &[u8]) -> Self {
        Self::from_le_bytes(bytes.try_into().expect("slice not limb-sized"))
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use proptest::prelude::*;

    prop_compose! {
        fn limb()(inner in any::<Word>()) -> Limb {
            Limb(inner)
        }
    }

    proptest! {
        #[test]
        fn roundtrip(a in limb()) {
            assert_eq!(a, Limb::from_be_bytes(a.to_be_bytes()));
            assert_eq!(a, Limb::from_le_bytes(a.to_le_bytes()));
        }
    }

    proptest! {
        #[test]
        fn reverse(a in limb()) {
            let mut bytes = a.to_be_bytes();
            bytes.reverse();
            assert_eq!(a, Limb::from_le_bytes(bytes));

            let mut bytes = a.to_le_bytes();
            bytes.reverse();
            assert_eq!(a, Limb::from_be_bytes(bytes));
        }
    }
}
