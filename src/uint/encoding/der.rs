//! Support for decoding/encoding [`Uint`] as an ASN.1 DER `INTEGER`.

use crate::{ArrayEncoding, Encoding, Limb, Uint, hybrid_array::Array};
use ::der::{
    DecodeValue, EncodeValue, FixedTag, Length, Tag,
    asn1::{AnyRef, UintRef},
};

impl<'a, const LIMBS: usize> TryFrom<AnyRef<'a>> for Uint<LIMBS>
where
    Uint<LIMBS>: ArrayEncoding,
{
    type Error = der::Error;

    fn try_from(any: AnyRef<'a>) -> der::Result<Uint<LIMBS>> {
        UintRef::try_from(any)?.try_into()
    }
}

impl<'a, const LIMBS: usize> TryFrom<UintRef<'a>> for Uint<LIMBS>
where
    Uint<LIMBS>: ArrayEncoding,
{
    type Error = der::Error;

    fn try_from(bytes: UintRef<'a>) -> der::Result<Uint<LIMBS>> {
        let mut array = Array::default();
        let offset = array.len().saturating_sub(bytes.len().try_into()?);
        array[offset..].copy_from_slice(bytes.as_bytes());
        Ok(Uint::from_be_byte_array(array))
    }
}

impl<'a, const LIMBS: usize> DecodeValue<'a> for Uint<LIMBS>
where
    Uint<LIMBS>: ArrayEncoding,
{
    type Error = der::Error;

    fn decode_value<R: der::Reader<'a>>(reader: &mut R, header: der::Header) -> der::Result<Self> {
        UintRef::decode_value(reader, header)?.try_into()
    }
}

impl<const LIMBS: usize> EncodeValue for Uint<LIMBS>
where
    Uint<LIMBS>: ArrayEncoding,
{
    fn value_len(&self) -> der::Result<Length> {
        Ok(self.count_der_be_bytes().into())
    }

    fn encode_value(&self, encoder: &mut impl der::Writer) -> der::Result<()> {
        let array = self.to_be_byte_array();
        UintRef::new(&array)?.encode_value(encoder)
    }
}

impl<const LIMBS: usize> FixedTag for Uint<LIMBS>
where
    Uint<LIMBS>: ArrayEncoding,
{
    const TAG: Tag = Tag::Integer;
}

impl<const LIMBS: usize> Uint<LIMBS> {
    /// Counts bytes in DER ASN.1 `INTEGER` big-endian encoding, without leading zero bytes.
    #[inline]
    pub(crate) fn count_der_be_bytes(&self) -> u32 {
        // Number of 0x00 bytes (also index of first non-zero byte)
        let leading_zero_bytes = self.leading_zero_be_bytes();

        // Limbs indexed in reverse
        let limb_index = LIMBS
            .saturating_sub(1)
            .saturating_sub(leading_zero_bytes as usize / Limb::BYTES);

        // Limb bytes encoded as big-endian
        let first_nonzero_byte = self
            .limbs
            .get(limb_index)
            .cloned()
            .map(|limb| limb.to_be_bytes()[leading_zero_bytes as usize % Limb::BYTES])
            .unwrap_or(0x00);

        // Does the given integer need a leading zero?
        let needs_leading_zero = first_nonzero_byte >= 0x80;

        // Number of bytes in all limbs
        let max_len = (Limb::BYTES * LIMBS) as u32;

        // If all bytes are zeros:
        if leading_zero_bytes == max_len {
            // we're encoding 0x00, so one byte remains
            1
        } else {
            max_len
                .saturating_sub(leading_zero_bytes)
                .wrapping_add(needs_leading_zero as u32)
        }
    }
}

#[cfg(test)]
pub mod test {
    use crate::{ArrayEncoding, U128, Uint};
    use der::EncodeValue;

    fn assert_valid_value_len<const LIMBS: usize>(n: &Uint<LIMBS>) -> der::Result<()>
    where
        Uint<LIMBS>: ArrayEncoding,
    {
        let mut buf = [0u8; 128];
        let encoded_value = {
            let mut writer = der::SliceWriter::new(&mut buf);
            n.encode_value(&mut writer)?;
            writer.finish()?
        };

        let computed_len: u32 = n.value_len()?.into();
        let encoded_len: u32 = encoded_value.len() as u32;
        assert_eq!(
            computed_len, encoded_len,
            "computed_len: {computed_len}, encoded_len: {encoded_len}, n:{n:?}"
        );
        Ok(())
    }

    fn assert_valid_value_len_hex(hex_uint: &str) {
        let n = U128::from_str_radix_vartime(hex_uint, 16).expect("error decoding");
        assert_valid_value_len(&n).expect("error from der");
    }
    #[test]
    fn encode_uint() {
        assert_valid_value_len_hex("00");
        assert_valid_value_len_hex("10");
        assert_valid_value_len_hex("3210");

        assert_valid_value_len_hex("00000000000000007fdcba9876543210");
        assert_valid_value_len_hex("0000000000000000fedcba9876543210");
        assert_valid_value_len_hex("0000000000000010fedcba9876543210");
        assert_valid_value_len_hex("0000000000000080fedcba9876543210");

        assert_valid_value_len_hex("0000008076543210fedcba9876543210");
        assert_valid_value_len_hex("00dcba9876543210fedcba9876543210");
        assert_valid_value_len_hex("0fdcba9876543210fedcba9876543210");
        assert_valid_value_len_hex("7fdcba9876543210fedcba9876543210");
        assert_valid_value_len_hex("fedcba9876543210fedcba9876543210");
    }
}
