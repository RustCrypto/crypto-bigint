//! Interop support for `hybrid-array`

use crate::{EncodedUint, Encoding, Integer, Limb};
use core::ops::Add;
use hybrid_array::{Array, ArrayN, ArraySize, typenum::Unsigned};

/// Alias for a byte array whose size is defined by [`ArrayEncoding::ByteSize`].
pub type ByteArray<T> = Array<u8, <T as ArrayEncoding>::ByteSize>;

/// Support for encoding a big integer as a `Array`.
pub trait ArrayEncoding: Encoding {
    /// Size of a byte array which encodes a big integer.
    type ByteSize: ArraySize + Add + Eq + Ord + Unsigned;

    /// Deserialize from a big-endian byte array.
    fn from_be_byte_array(bytes: ByteArray<Self>) -> Self;

    /// Deserialize from a little-endian byte array.
    fn from_le_byte_array(bytes: ByteArray<Self>) -> Self;

    /// Serialize to a big-endian byte array.
    fn to_be_byte_array(&self) -> ByteArray<Self>;

    /// Serialize to a little-endian byte array.
    fn to_le_byte_array(&self) -> ByteArray<Self>;
}

/// Support for decoding a `Array` as a big integer.
pub trait ArrayDecoding {
    /// Big integer which decodes a `Array`.
    type Output: ArrayEncoding + Integer;

    /// Deserialize from a big-endian `Array`.
    fn into_uint_be(self) -> Self::Output;

    /// Deserialize from a little-endian `Array`.
    fn into_uint_le(self) -> Self::Output;
}

macro_rules! from_impls_for_encoded_uint {
    ( $($nlimbs:expr),+ ) => {
        $(
            impl From<EncodedUint<$nlimbs>> for ArrayN<u8, { $nlimbs * Limb::BYTES }> {
                #[inline]
                fn from(input: EncodedUint<$nlimbs>) -> Self {
                    let mut output = Self::default();
                    output.as_mut_slice().copy_from_slice(input.as_ref());
                    output
                }
            }

            impl From<ArrayN<u8, { $nlimbs * Limb::BYTES }>> for EncodedUint<$nlimbs> {
                #[inline]
                fn from(input: ArrayN<u8, { $nlimbs * Limb::BYTES }>) -> Self {
                    let mut output = Self::default();
                    output.as_mut().copy_from_slice(input.as_ref());
                    output
                }
            }
        )+
    };
}

// Support up to 16 limbs for now (chosen somewhat arbitrarily)
from_impls_for_encoded_uint!(1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16);

#[cfg(test)]
mod tests {
    const LIMBS: usize = 4;
    const BYTES: usize = super::Limb::BYTES * LIMBS;

    type Array = super::ArrayN<u8, { BYTES }>;
    type EncodedUint = super::EncodedUint<LIMBS>;

    const ARRAY: Array = {
        let mut i = 0;
        let mut ret = [0u8; BYTES];
        while i < BYTES {
            ret[i] = i as u8;
            i += 1;
        }
        hybrid_array::Array(ret)
    };

    #[test]
    fn from_impls_for_encoded_uint() {
        let encoded_uint = EncodedUint::from(ARRAY);
        assert_eq!(encoded_uint.as_ref(), ARRAY.as_slice());

        let array = Array::from(encoded_uint);
        assert_eq!(array, ARRAY);
    }
}
