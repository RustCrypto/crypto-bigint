//! Support for serdect on [`BoxedUint`]

use serdect::serde::{de, Deserialize, Deserializer, Serialize, Serializer};

use crate::BoxedUint;

impl<'de> Deserialize<'de> for BoxedUint {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let mut buffer = Self::zero().to_le_bytes();
        serdect::array::deserialize_hex_or_bin(buffer.as_mut(), deserializer)?;

        let bits_in = buffer.len() * 8;

        if bits_in > u32::MAX as usize {
            return Err(de::Error::custom(
                "Deserialize input overflows BoxedUint u32 bits length",
            ));
        }

        Self::from_le_slice(&buffer, bits_in as u32)
            .map_err(|_| de::Error::custom("Deserialize error"))
    }
}

#[cfg(feature = "serde")]
impl Serialize for BoxedUint {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        serdect::array::serialize_hex_lower_or_bin(&self.to_le_bytes(), serializer)
    }
}

#[cfg(test)]
mod tests {
    use super::BoxedUint;

    #[test]
    #[cfg(target_pointer_width = "64")]
    fn serde() {
        #[allow(trivial_numeric_casts)]
        let test: BoxedUint = BoxedUint::from_be_hex("7711223344556600", 64).unwrap();

        let serialized = bincode::serialize(&test).unwrap();
        let deserialized: BoxedUint = bincode::deserialize(&serialized).unwrap();

        assert_eq!(test, deserialized);
    }

    #[test]
    #[cfg(target_pointer_width = "64")]
    fn serde_owned() {
        #[allow(trivial_numeric_casts)]
        let test: BoxedUint = BoxedUint::from_be_hex("7711223344556600", 64).unwrap();

        let serialized = bincode::serialize(&test).unwrap();
        let deserialized: BoxedUint = bincode::deserialize_from(serialized.as_slice()).unwrap();

        assert_eq!(test, deserialized);
    }

    #[test]
    #[cfg(target_pointer_width = "32")]
    fn from_le_slice_eq() {
        let test = hex!("7766554433221100");
        let box_uint = BoxedUint::from_le_slice(&bytes, 64).unwrap();

        let serialized = bincode::serialize(&box_uint).unwrap();
        let deserialized: BoxedUint = bincode::deserialize_from(serialized.as_slice()).unwrap();

        assert_eq!(
            deserialized.as_limbs(),
            &[Limb(0x44556677), Limb(0x00112233)]
        );
    }
}
