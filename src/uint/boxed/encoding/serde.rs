use serdect::serde::{Deserialize, Deserializer, Serialize, Serializer, de::Error};

use crate::BoxedUint;

impl<'de> Deserialize<'de> for BoxedUint {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let slice = serdect::slice::deserialize_hex_or_bin_vec(deserializer)?;
        Self::from_le_slice(&slice, slice.len() as u32 * 8).map_err(Error::custom)
    }
}

impl Serialize for BoxedUint {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        serdect::slice::serialize_hex_lower_or_bin(&self.to_le_bytes(), serializer)
    }
}

#[cfg(test)]
mod tests {
    use super::BoxedUint;

    #[test]
    fn serde_roundabout() {
        let n = BoxedUint::from(11223344u64);
        let ser = serde_json::to_string(&n).unwrap();
        let de: BoxedUint = serde_json::from_str(&ser).unwrap();
        assert_eq!(n, de);
    }

    #[test]
    #[cfg(target_pointer_width = "64")]
    fn serde() {
        let test: BoxedUint = BoxedUint::from_be_hex("7711223344556600", 64).unwrap();

        let serialized = bincode::serialize(&test).unwrap();
        let deserialized: BoxedUint = bincode::deserialize(&serialized).unwrap();

        assert_eq!(test, deserialized);
    }

    #[test]
    #[cfg(target_pointer_width = "64")]
    fn serde_owned() {
        let test: BoxedUint = BoxedUint::from_be_hex("7711223344556600", 64).unwrap();

        let serialized = bincode::serialize(&test).unwrap();
        let deserialized: BoxedUint = bincode::deserialize_from(serialized.as_slice()).unwrap();

        assert_eq!(test, deserialized);
    }

    #[test]
    #[cfg(target_pointer_width = "32")]
    fn from_le_slice_eq_test() {
        let bytes = hex!("7766554433221100");
        let box_uint = BoxedUint::from_le_slice(&bytes, 64).unwrap();

        let serialized = bincode::serialize(&box_uint).unwrap();
        let deserialized: BoxedUint = bincode::deserialize_from(serialized.as_slice()).unwrap();

        assert_eq!(
            deserialized.as_limbs(),
            &[Limb(0x44556677), Limb(0x00112233)]
        );
    }
}
