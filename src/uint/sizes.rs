//! Types used to determine valid size conversions for `Uint`.

/// A type representing the concatenation of two limb slices.
#[derive(Debug, Copy, Clone)]
pub struct ConcatSize<const LO: usize, const HI: usize>;

/// A type representing the removal of one limb slice from another.
#[derive(Debug, Copy, Clone)]
pub struct SplitSize<const WIDE: usize, const LO: usize>;

/// A type representing the encoded size of type in bytes.
#[derive(Debug, Copy, Clone)]
pub struct EncodedSize<const BYTES: usize>;
