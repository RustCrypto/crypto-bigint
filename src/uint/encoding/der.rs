//! Support for decoding/encoding [`UInt`] as an ASN.1 DER `INTEGER`.

use crate::{generic_array::GenericArray, ArrayEncoding, UInt};
use ::der::{
    asn1::{Any, UIntBytes},
    EncodeValue, Encoder, FixedTag, Length, Tag,
};

#[cfg(feature = "der")]
#[cfg_attr(docsrs, doc(cfg(feature = "der")))]
impl<'a, const LIMBS: usize> TryFrom<Any<'a>> for UInt<LIMBS>
where
    UInt<LIMBS>: ArrayEncoding,
{
    type Error = der::Error;

    fn try_from(any: Any<'a>) -> der::Result<UInt<LIMBS>> {
        UIntBytes::try_from(any)?.try_into()
    }
}

#[cfg(feature = "der")]
#[cfg_attr(docsrs, doc(cfg(feature = "der")))]
impl<'a, const LIMBS: usize> TryFrom<UIntBytes<'a>> for UInt<LIMBS>
where
    UInt<LIMBS>: ArrayEncoding,
{
    type Error = der::Error;

    fn try_from(bytes: UIntBytes<'a>) -> der::Result<UInt<LIMBS>> {
        let mut array = GenericArray::default();
        let offset = array.len().saturating_sub(bytes.len().try_into()?);
        array[offset..].copy_from_slice(bytes.as_bytes());
        Ok(UInt::from_be_byte_array(array))
    }
}

#[cfg(feature = "der")]
#[cfg_attr(docsrs, doc(cfg(feature = "der")))]
impl<const LIMBS: usize> EncodeValue for UInt<LIMBS>
where
    UInt<LIMBS>: ArrayEncoding,
{
    fn value_len(&self) -> der::Result<Length> {
        // TODO(tarcieri): more efficient length calculation
        let array = self.to_be_byte_array();
        UIntBytes::new(&array)?.value_len()
    }

    fn encode_value(&self, encoder: &mut Encoder<'_>) -> der::Result<()> {
        let array = self.to_be_byte_array();
        UIntBytes::new(&array)?.encode_value(encoder)
    }
}

#[cfg(feature = "der")]
#[cfg_attr(docsrs, doc(cfg(feature = "der")))]
impl<const LIMBS: usize> FixedTag for UInt<LIMBS>
where
    UInt<LIMBS>: ArrayEncoding,
{
    const TAG: Tag = Tag::Integer;
}
