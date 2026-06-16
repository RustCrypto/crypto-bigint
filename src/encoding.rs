//! Shared encoding support.

/// Byte order used when encoding/decoding field elements as bytestrings.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ByteOrder {
    /// Big endian.
    BigEndian,

    /// Little endian.
    LittleEndian,
}
