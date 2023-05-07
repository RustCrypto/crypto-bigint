//! Big unsigned integers.

#![allow(
    clippy::needless_range_loop,
    clippy::many_single_char_names,
    clippy::derive_hash_xor_eq
)]

#[macro_use]
mod concat;
#[macro_use]
mod split;

mod add;
mod add_mod;
mod bit_and;
mod bit_not;
mod bit_or;
mod bit_xor;
mod bits;
mod cmp;
mod div;
pub(crate) mod div_limb;
mod encoding;
mod from;
mod inv_mod;
mod mul;
mod mul_mod;
mod neg;
mod neg_mod;
mod resize;
mod shl;
mod shr;
mod sqrt;
mod sub;
mod sub_mod;

/// Implements modular arithmetic for constant moduli.
pub mod modular;

#[cfg(feature = "generic-array")]
mod array;

#[cfg(feature = "rand_core")]
mod rand;

use crate::{Bounded, Concat, Encoding, Integer, Limb, Split, Word, Zero};
use core::fmt;
use subtle::{Choice, ConditionallySelectable};

#[cfg(feature = "serde")]
use serdect::serde::{Deserialize, Deserializer, Serialize, Serializer};

#[cfg(feature = "zeroize")]
use zeroize::DefaultIsZeroes;

/// Big unsigned integer.
///
/// Generic over the given number of `LIMBS`
///
/// # Encoding support
/// This type supports many different types of encodings, either via the
/// [`Encoding`][`crate::Encoding`] trait or various `const fn` decoding and
/// encoding functions that can be used with [`Uint`] constants.
///
/// Optional crate features for encoding (off-by-default):
/// - `generic-array`: enables [`ArrayEncoding`][`crate::ArrayEncoding`] trait which can be used to
///   [`Uint`] as `GenericArray<u8, N>` and a [`ArrayDecoding`][`crate::ArrayDecoding`] trait which
///   can be used to `GenericArray<u8, N>` as [`Uint`].
/// - `rlp`: support for [Recursive Length Prefix (RLP)][RLP] encoding.
///
/// [RLP]: https://eth.wiki/fundamentals/rlp
// TODO(tarcieri): make generic around a specified number of bits.
#[derive(Copy, Clone, Hash)]
pub struct Uint<const LIMBS: usize> {
    /// Inner limb array. Stored from least significant to most significant.
    limbs: [Limb; LIMBS],
}

impl<const LIMBS: usize> Uint<LIMBS> {
    /// The value `0`.
    pub const ZERO: Self = Self::from_u8(0);

    /// The value `1`.
    pub const ONE: Self = Self::from_u8(1);

    /// Maximum value this [`Uint`] can express.
    pub const MAX: Self = Self {
        limbs: [Limb::MAX; LIMBS],
    };

    /// Total size of the represented integer in bits.
    pub const BITS: usize = LIMBS * Limb::BITS;

    /// Total size of the represented integer in bytes.
    pub const BYTES: usize = LIMBS * Limb::BYTES;

    /// The number of limbs used on this platform.
    pub const LIMBS: usize = LIMBS;

    /// Const-friendly [`Uint`] constructor.
    pub const fn new(limbs: [Limb; LIMBS]) -> Self {
        Self { limbs }
    }

    /// Create a [`Uint`] from an array of [`Word`]s (i.e. word-sized unsigned
    /// integers).
    #[inline]
    pub const fn from_words(arr: [Word; LIMBS]) -> Self {
        let mut limbs = [Limb::ZERO; LIMBS];
        let mut i = 0;

        while i < LIMBS {
            limbs[i] = Limb(arr[i]);
            i += 1;
        }

        Self { limbs }
    }

    /// Create an array of [`Word`]s (i.e. word-sized unsigned integers) from
    /// a [`Uint`].
    #[inline]
    pub const fn to_words(self) -> [Word; LIMBS] {
        let mut arr = [0; LIMBS];
        let mut i = 0;

        while i < LIMBS {
            arr[i] = self.limbs[i].0;
            i += 1;
        }

        arr
    }

    /// Borrow the inner limbs as an array of [`Word`]s.
    pub const fn as_words(&self) -> &[Word; LIMBS] {
        // SAFETY: `Limb` is a `repr(transparent)` newtype for `Word`
        #[allow(trivial_casts, unsafe_code)]
        unsafe {
            &*((&self.limbs as *const _) as *const [Word; LIMBS])
        }
    }

    /// Borrow the inner limbs as a mutable array of [`Word`]s.
    pub fn as_words_mut(&mut self) -> &mut [Word; LIMBS] {
        // SAFETY: `Limb` is a `repr(transparent)` newtype for `Word`
        #[allow(trivial_casts, unsafe_code)]
        unsafe {
            &mut *((&mut self.limbs as *mut _) as *mut [Word; LIMBS])
        }
    }

    /// Borrow the limbs of this [`Uint`].
    pub const fn as_limbs(&self) -> &[Limb; LIMBS] {
        &self.limbs
    }

    /// Borrow the limbs of this [`Uint`] mutably.
    pub fn as_limbs_mut(&mut self) -> &mut [Limb; LIMBS] {
        &mut self.limbs
    }

    /// Convert this [`Uint`] into its inner limbs.
    pub const fn to_limbs(self) -> [Limb; LIMBS] {
        self.limbs
    }
}

impl<const LIMBS: usize> AsRef<[Word; LIMBS]> for Uint<LIMBS> {
    fn as_ref(&self) -> &[Word; LIMBS] {
        self.as_words()
    }
}

impl<const LIMBS: usize> AsMut<[Word; LIMBS]> for Uint<LIMBS> {
    fn as_mut(&mut self) -> &mut [Word; LIMBS] {
        self.as_words_mut()
    }
}

impl<const LIMBS: usize> AsRef<[Limb]> for Uint<LIMBS> {
    fn as_ref(&self) -> &[Limb] {
        self.as_limbs()
    }
}

impl<const LIMBS: usize> AsMut<[Limb]> for Uint<LIMBS> {
    fn as_mut(&mut self) -> &mut [Limb] {
        self.as_limbs_mut()
    }
}

impl<const LIMBS: usize> ConditionallySelectable for Uint<LIMBS> {
    fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
        let mut limbs = [Limb::ZERO; LIMBS];

        for i in 0..LIMBS {
            limbs[i] = Limb::conditional_select(&a.limbs[i], &b.limbs[i], choice);
        }

        Self { limbs }
    }
}

impl<const LIMBS: usize> Default for Uint<LIMBS> {
    fn default() -> Self {
        Self::ZERO
    }
}

impl<const LIMBS: usize> Integer for Uint<LIMBS> {
    const ONE: Self = Self::ONE;
    const MAX: Self = Self::MAX;
    const BITS: usize = Self::BITS;
    const BYTES: usize = Self::BYTES;
    const LIMBS: usize = Self::LIMBS;

    fn is_odd(&self) -> Choice {
        self.limbs
            .first()
            .map(|limb| limb.is_odd())
            .unwrap_or_else(|| Choice::from(0))
    }
}

impl<const LIMBS: usize> Zero for Uint<LIMBS> {
    const ZERO: Self = Self::ZERO;
}

impl<const LIMBS: usize> Bounded for Uint<LIMBS> {
    const BITS: usize = Self::BITS;
    const BYTES: usize = Self::BYTES;
}

impl<const LIMBS: usize> fmt::Debug for Uint<LIMBS> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Uint(0x{self:X})")
    }
}

impl<const LIMBS: usize> fmt::Display for Uint<LIMBS> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::UpperHex::fmt(self, f)
    }
}

impl<const LIMBS: usize> fmt::LowerHex for Uint<LIMBS> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for limb in self.limbs.iter().rev() {
            fmt::LowerHex::fmt(limb, f)?;
        }
        Ok(())
    }
}

impl<const LIMBS: usize> fmt::UpperHex for Uint<LIMBS> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for limb in self.limbs.iter().rev() {
            fmt::UpperHex::fmt(limb, f)?;
        }
        Ok(())
    }
}

#[cfg(feature = "serde")]
impl<'de, const LIMBS: usize> Deserialize<'de> for Uint<LIMBS>
where
    Uint<LIMBS>: Encoding,
{
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let mut buffer = Self::ZERO.to_le_bytes();
        serdect::array::deserialize_hex_or_bin(buffer.as_mut(), deserializer)?;

        Ok(Self::from_le_bytes(buffer))
    }
}

#[cfg(feature = "serde")]
impl<const LIMBS: usize> Serialize for Uint<LIMBS>
where
    Uint<LIMBS>: Encoding,
{
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        serdect::array::serialize_hex_lower_or_bin(&Encoding::to_le_bytes(self), serializer)
    }
}

#[cfg(feature = "zeroize")]
impl<const LIMBS: usize> DefaultIsZeroes for Uint<LIMBS> {}

// TODO(tarcieri): use `const_evaluatable_checked` when stable to make generic around bits.
macro_rules! impl_uint_aliases {
    ($(($name:ident, $bits:expr, $doc:expr)),+) => {
        $(
            #[doc = $doc]
            #[doc="unsigned big integer."]
            pub type $name = Uint<{nlimbs!($bits)}>;

            impl Encoding for $name {

                type Repr = [u8; $bits / 8];

                #[inline]
                fn from_be_bytes(bytes: Self::Repr) -> Self {
                    Self::from_be_slice(&bytes)
                }

                #[inline]
                fn from_le_bytes(bytes: Self::Repr) -> Self {
                    Self::from_le_slice(&bytes)
                }

                #[inline]
                fn to_be_bytes(&self) -> Self::Repr {
                    let mut result = [0u8; $bits / 8];
                    self.write_be_bytes(&mut result);
                    result
                }

                #[inline]
                fn to_le_bytes(&self) -> Self::Repr {
                    let mut result = [0u8; $bits / 8];
                    self.write_le_bytes(&mut result);
                    result
                }
            }
        )+
     };
}

#[cfg(feature = "extra-sizes")]
impl_uint_aliases! {
    (U64, 64, "64-bit"),
    (U128, 128, "128-bit"),
    (U192, 192, "192-bit"),
    (U256, 256, "256-bit"),
    (U320, 320, "320-bit"),
    (U384, 384, "384-bit"),
    (U448, 448, "448-bit"),
    (U512, 512, "512-bit"),
    (U576, 576, "576-bit"),
    (U640, 640, "640-bit"),
    (U704, 704, "704-bit"),
    (U768, 768, "768-bit"),
    (U832, 832, "832-bit"),
    (U896, 896, "896-bit"),
    (U960, 960, "960-bit"),
    (U1024, 1024, "1024-bit"),
    (U1088, 1088, "1088-bit"),
    (U1152, 1152, "1152-bit"),
    (U1216, 1216, "1216-bit"),
    (U1280, 1280, "1280-bit"),
    (U1344, 1344, "1344-bit"),
    (U1408, 1408, "1408-bit"),
    (U1472, 1472, "1472-bit"),
    (U1536, 1536, "1536-bit"),
    (U1600, 1600, "1600-bit"),
    (U1664, 1664, "1664-bit"),
    (U1728, 1728, "1728-bit"),
    (U1792, 1792, "1792-bit"),
    (U1856, 1856, "1856-bit"),
    (U1920, 1920, "1920-bit"),
    (U1984, 1984, "1984-bit"),
    (U2048, 2048, "2048-bit"),
    (U2112, 2112, "2112-bit"),
    (U2176, 2176, "2176-bit"),
    (U2240, 2240, "2240-bit"),
    (U2304, 2304, "2304-bit"),
    (U2368, 2368, "2368-bit"),
    (U2432, 2432, "2432-bit"),
    (U2496, 2496, "2496-bit"),
    (U2560, 2560, "2560-bit"),
    (U2624, 2624, "2624-bit"),
    (U2688, 2688, "2688-bit"),
    (U2752, 2752, "2752-bit"),
    (U2816, 2816, "2816-bit"),
    (U2880, 2880, "2880-bit"),
    (U2944, 2944, "2944-bit"),
    (U3008, 3008, "3008-bit"),
    (U3072, 3072, "3072-bit"),
    (U3136, 3136, "3136-bit"),
    (U3200, 3200, "3200-bit"),
    (U3264, 3264, "3264-bit"),
    (U3328, 3328, "3328-bit"),
    (U3392, 3392, "3392-bit"),
    (U3456, 3456, "3456-bit"),
    (U3520, 3520, "3520-bit"),
    (U3584, 3584, "3584-bit"),
    (U3648, 3648, "3648-bit"),
    (U3712, 3712, "3712-bit"),
    (U3776, 3776, "3776-bit"),
    (U3840, 3840, "3840-bit"),
    (U3904, 3904, "3904-bit"),
    (U3968, 3968, "3968-bit"),
    (U4032, 4032, "4032-bit"),
    (U4096, 4096, "4096-bit"),
    (U4160, 4160, "4160-bit"),
    (U4224, 4224, "4224-bit"),
    (U4288, 4288, "4288-bit"),
    (U4352, 4352, "4352-bit"),
    (U4416, 4416, "4416-bit"),
    (U4480, 4480, "4480-bit"),
    (U4544, 4544, "4544-bit"),
    (U4608, 4608, "4608-bit"),
    (U4672, 4672, "4672-bit"),
    (U4736, 4736, "4736-bit"),
    (U4800, 4800, "4800-bit"),
    (U4864, 4864, "4864-bit"),
    (U4928, 4928, "4928-bit"),
    (U4992, 4992, "4992-bit"),
    (U5056, 5056, "5056-bit"),
    (U5120, 5120, "5120-bit"),
    (U5184, 5184, "5184-bit"),
    (U5248, 5248, "5248-bit"),
    (U5312, 5312, "5312-bit"),
    (U5376, 5376, "5376-bit"),
    (U5440, 5440, "5440-bit"),
    (U5504, 5504, "5504-bit"),
    (U5568, 5568, "5568-bit"),
    (U5632, 5632, "5632-bit"),
    (U5696, 5696, "5696-bit"),
    (U5760, 5760, "5760-bit"),
    (U5824, 5824, "5824-bit"),
    (U5888, 5888, "5888-bit"),
    (U5952, 5952, "5952-bit"),
    (U6016, 6016, "6016-bit"),
    (U6080, 6080, "6080-bit"),
    (U6144, 6144, "6144-bit"),
    (U6208, 6208, "6208-bit"),
    (U6272, 6272, "6272-bit"),
    (U6336, 6336, "6336-bit"),
    (U6400, 6400, "6400-bit"),
    (U6464, 6464, "6464-bit"),
    (U6528, 6528, "6528-bit"),
    (U6592, 6592, "6592-bit"),
    (U6656, 6656, "6656-bit"),
    (U6720, 6720, "6720-bit"),
    (U6784, 6784, "6784-bit"),
    (U6848, 6848, "6848-bit"),
    (U6912, 6912, "6912-bit"),
    (U6976, 6976, "6976-bit"),
    (U7040, 7040, "7040-bit"),
    (U7104, 7104, "7104-bit"),
    (U7168, 7168, "7168-bit"),
    (U7232, 7232, "7232-bit"),
    (U7296, 7296, "7296-bit"),
    (U7360, 7360, "7360-bit"),
    (U7424, 7424, "7424-bit"),
    (U7488, 7488, "7488-bit"),
    (U7552, 7552, "7552-bit"),
    (U7616, 7616, "7616-bit"),
    (U7680, 7680, "7680-bit"),
    (U7744, 7744, "7744-bit"),
    (U7808, 7808, "7808-bit"),
    (U7872, 7872, "7872-bit"),
    (U7936, 7936, "7936-bit"),
    (U8000, 8000, "8000-bit"),
    (U8064, 8064, "8064-bit"),
    (U8128, 8128, "8128-bit"),
    (U8192, 8192, "8192-bit")
}

#[cfg(not(feature = "extra-sizes"))]
// TODO(tarcieri): use `const_evaluatable_checked` when stable to make generic around bits.
impl_uint_aliases! {
    (U64, 64, "64-bit"),
    (U128, 128, "128-bit"),
    (U192, 192, "192-bit"),
    (U256, 256, "256-bit"),
    (U320, 320, "320-bit"),
    (U384, 384, "384-bit"),
    (U448, 448, "448-bit"),
    (U512, 512, "512-bit"),
    (U576, 576, "576-bit"),
    (U640, 640, "640-bit"),
    (U768, 768, "768-bit"),
    (U896, 896, "896-bit"),
    (U1024, 1024, "1024-bit"),
    (U1280, 1280, "1280-bit"),
    (U1536, 1536, "1536-bit"),
    (U1792, 1792, "1792-bit"),
    (U2048, 2048, "2048-bit"),
    (U3072, 3072, "3072-bit"),
    (U3584, 3584, "3584-bit"),
    (U4096, 4096, "4096-bit"),
    (U6144, 6144, "6144-bit"),
    (U8192, 8192, "8192-bit")
}

#[cfg(target_pointer_width = "32")]
impl_uint_aliases! {
    (U224, 224, "224-bit"), // For NIST P-224
    (U544, 544, "544-bit")  // For NIST P-521
}

#[cfg(feature = "extra-sizes")]
impl_concat! {
    (U64, 64),
    (U128, 128),
    (U192, 192),
    (U256, 256),
    (U320, 320),
    (U384, 384),
    (U448, 448),
    (U512, 512),
    (U576, 576),
    (U640, 640),
    (U704, 704),
    (U768, 768),
    (U832, 832),
    (U896, 896),
    (U960, 960),
    (U1024, 1024),
    (U1088, 1088),
    (U1152, 1152),
    (U1216, 1216),
    (U1280, 1280),
    (U1344, 1344),
    (U1408, 1408),
    (U1472, 1472),
    (U1536, 1536),
    (U1600, 1600),
    (U1664, 1664),
    (U1728, 1728),
    (U1792, 1792),
    (U1856, 1856),
    (U1920, 1920),
    (U1984, 1984),
    (U2048, 2048),
    (U2112, 2112),
    (U2176, 2176),
    (U2240, 2240),
    (U2304, 2304),
    (U2368, 2368),
    (U2432, 2432),
    (U2496, 2496),
    (U2560, 2560),
    (U2624, 2624),
    (U2688, 2688),
    (U2752, 2752),
    (U2816, 2816),
    (U2880, 2880),
    (U2944, 2944),
    (U3008, 3008),
    (U3072, 3072),
    (U3136, 3136),
    (U3200, 3200),
    (U3264, 3264),
    (U3328, 3328),
    (U3392, 3392),
    (U3456, 3456),
    (U3520, 3520),
    (U3584, 3584),
    (U3648, 3648),
    (U3712, 3712),
    (U3776, 3776),
    (U3840, 3840),
    (U3904, 3904),
    (U3968, 3968),
    (U4032, 4032),
    (U4096, 4096),
    (U4160, 4160),
    (U4224, 4224),
    (U4288, 4288),
    (U4352, 4352),
    (U4416, 4416),
    (U4480, 4480),
    (U4544, 4544),
    (U4608, 4608),
    (U4672, 4672),
    (U4736, 4736),
    (U4800, 4800),
    (U4864, 4864),
    (U4928, 4928),
    (U4992, 4992),
    (U5056, 5056),
    (U5120, 5120),
    (U5184, 5184),
    (U5248, 5248),
    (U5312, 5312),
    (U5376, 5376),
    (U5440, 5440),
    (U5504, 5504),
    (U5568, 5568),
    (U5632, 5632),
    (U5696, 5696),
    (U5760, 5760),
    (U5824, 5824),
    (U5888, 5888),
    (U5952, 5952),
    (U6016, 6016),
    (U6080, 6080),
    (U6144, 6144),
    (U6208, 6208),
    (U6272, 6272),
    (U6336, 6336),
    (U6400, 6400),
    (U6464, 6464),
    (U6528, 6528),
    (U6592, 6592),
    (U6656, 6656),
    (U6720, 6720),
    (U6784, 6784),
    (U6848, 6848),
    (U6912, 6912),
    (U6976, 6976),
    (U7040, 7040),
    (U7104, 7104),
    (U7168, 7168),
    (U7232, 7232),
    (U7296, 7296),
    (U7360, 7360),
    (U7424, 7424),
    (U7488, 7488),
    (U7552, 7552),
    (U7616, 7616),
    (U7680, 7680),
    (U7744, 7744),
    (U7808, 7808),
    (U7872, 7872),
    (U7936, 7936),
    (U8000, 8000),
    (U8064, 8064),
    (U8128, 8128),
    (U8192, 8192)
}

#[cfg(not(feature = "extra-sizes"))]
// TODO(tarcieri): use `const_evaluatable_checked` when stable to make generic around bits.
impl_concat! {
    (U64, 64),
    (U128, 128),
    (U192, 192),
    (U256, 256),
    (U320, 320),
    (U384, 384),
    (U448, 448),
    (U512, 512),
    (U640, 640),
    (U768, 768),
    (U896, 896),
    (U1024, 1024),
    (U1536, 1536),
    (U1792, 1792),
    (U2048, 2048),
    (U3072, 3072),
    (U4096, 4096)
}

#[cfg(feature = "extra-sizes")]
impl_split! {
    (U64, 64),
    (U128, 128),
    (U192, 192),
    (U256, 256),
    (U320, 320),
    (U384, 384),
    (U448, 448),
    (U512, 512),
    (U576, 576),
    (U640, 640),
    (U704, 704),
    (U768, 768),
    (U832, 832),
    (U896, 896),
    (U960, 960),
    (U1024, 1024),
    (U1088, 1088),
    (U1152, 1152),
    (U1216, 1216),
    (U1280, 1280),
    (U1344, 1344),
    (U1408, 1408),
    (U1472, 1472),
    (U1536, 1536),
    (U1600, 1600),
    (U1664, 1664),
    (U1728, 1728),
    (U1792, 1792),
    (U1856, 1856),
    (U1920, 1920),
    (U1984, 1984),
    (U2048, 2048),
    (U2112, 2112),
    (U2176, 2176),
    (U2240, 2240),
    (U2304, 2304),
    (U2368, 2368),
    (U2432, 2432),
    (U2496, 2496),
    (U2560, 2560),
    (U2624, 2624),
    (U2688, 2688),
    (U2752, 2752),
    (U2816, 2816),
    (U2880, 2880),
    (U2944, 2944),
    (U3008, 3008),
    (U3072, 3072),
    (U3136, 3136),
    (U3200, 3200),
    (U3264, 3264),
    (U3328, 3328),
    (U3392, 3392),
    (U3456, 3456),
    (U3520, 3520),
    (U3584, 3584),
    (U3648, 3648),
    (U3712, 3712),
    (U3776, 3776),
    (U3840, 3840),
    (U3904, 3904),
    (U3968, 3968),
    (U4032, 4032),
    (U4096, 4096),
    (U4160, 4160),
    (U4224, 4224),
    (U4288, 4288),
    (U4352, 4352),
    (U4416, 4416),
    (U4480, 4480),
    (U4544, 4544),
    (U4608, 4608),
    (U4672, 4672),
    (U4736, 4736),
    (U4800, 4800),
    (U4864, 4864),
    (U4928, 4928),
    (U4992, 4992),
    (U5056, 5056),
    (U5120, 5120),
    (U5184, 5184),
    (U5248, 5248),
    (U5312, 5312),
    (U5376, 5376),
    (U5440, 5440),
    (U5504, 5504),
    (U5568, 5568),
    (U5632, 5632),
    (U5696, 5696),
    (U5760, 5760),
    (U5824, 5824),
    (U5888, 5888),
    (U5952, 5952),
    (U6016, 6016),
    (U6080, 6080),
    (U6144, 6144),
    (U6208, 6208),
    (U6272, 6272),
    (U6336, 6336),
    (U6400, 6400),
    (U6464, 6464),
    (U6528, 6528),
    (U6592, 6592),
    (U6656, 6656),
    (U6720, 6720),
    (U6784, 6784),
    (U6848, 6848),
    (U6912, 6912),
    (U6976, 6976),
    (U7040, 7040),
    (U7104, 7104),
    (U7168, 7168),
    (U7232, 7232),
    (U7296, 7296),
    (U7360, 7360),
    (U7424, 7424),
    (U7488, 7488),
    (U7552, 7552),
    (U7616, 7616),
    (U7680, 7680),
    (U7744, 7744),
    (U7808, 7808),
    (U7872, 7872),
    (U7936, 7936),
    (U8000, 8000),
    (U8064, 8064),
    (U8128, 8128),
    (U8192, 8192)
}

#[cfg(not(feature = "extra-sizes"))]
// TODO(tarcieri): use `const_evaluatable_checked` when stable to make generic around bits.
impl_split! {
    (U128, 128),
    (U256, 256),
    (U384, 384),
    (U512, 512),
    (U640, 640),
    (U768, 768),
    (U896, 896),
    (U1024, 1024),
    (U1280, 1280),
    (U1536, 1536),
    (U1792, 1792),
    (U2048, 2048),
    (U3072, 3072),
    (U3584, 3584),
    (U4096, 4096),
    (U6144, 6144),
    (U8192, 8192)
}

#[cfg(test)]
mod tests {
    use crate::{Encoding, U128};
    use subtle::ConditionallySelectable;

    #[cfg(feature = "alloc")]
    use alloc::format;

    #[cfg(feature = "serde")]
    use crate::U64;

    #[cfg(feature = "alloc")]
    #[test]
    fn debug() {
        let hex = "AAAAAAAABBBBBBBBCCCCCCCCDDDDDDDD";
        let n = U128::from_be_hex(hex);

        assert_eq!(
            format!("{:?}", n),
            "Uint(0xAAAAAAAABBBBBBBBCCCCCCCCDDDDDDDD)"
        );
    }

    #[cfg(feature = "alloc")]
    #[test]
    fn display() {
        let hex = "AAAAAAAABBBBBBBBCCCCCCCCDDDDDDDD";
        let n = U128::from_be_hex(hex);

        use alloc::string::ToString;
        assert_eq!(hex, n.to_string());

        let hex = "AAAAAAAABBBBBBBB0000000000000000";
        let n = U128::from_be_hex(hex);
        assert_eq!(hex, n.to_string());

        let hex = "AAAAAAAABBBBBBBB00000000DDDDDDDD";
        let n = U128::from_be_hex(hex);
        assert_eq!(hex, n.to_string());

        let hex = "AAAAAAAABBBBBBBB0CCCCCCCDDDDDDDD";
        let n = U128::from_be_hex(hex);
        assert_eq!(hex, n.to_string());
    }

    #[test]
    fn from_bytes() {
        let a = U128::from_be_hex("AAAAAAAABBBBBBBB0CCCCCCCDDDDDDDD");

        let be_bytes = a.to_be_bytes();
        let le_bytes = a.to_le_bytes();
        for i in 0..16 {
            assert_eq!(le_bytes[i], be_bytes[15 - i]);
        }

        let a_from_be = U128::from_be_bytes(be_bytes);
        let a_from_le = U128::from_le_bytes(le_bytes);
        assert_eq!(a_from_be, a_from_le);
        assert_eq!(a_from_be, a);
    }

    #[test]
    fn conditional_select() {
        let a = U128::from_be_hex("00002222444466668888AAAACCCCEEEE");
        let b = U128::from_be_hex("11113333555577779999BBBBDDDDFFFF");

        let select_0 = U128::conditional_select(&a, &b, 0.into());
        assert_eq!(a, select_0);

        let select_1 = U128::conditional_select(&a, &b, 1.into());
        assert_eq!(b, select_1);
    }

    #[cfg(feature = "serde")]
    #[test]
    fn serde() {
        const TEST: U64 = U64::from_u64(0x0011223344556677);

        let serialized = bincode::serialize(&TEST).unwrap();
        let deserialized: U64 = bincode::deserialize(&serialized).unwrap();

        assert_eq!(TEST, deserialized);
    }

    #[cfg(feature = "serde")]
    #[test]
    fn serde_owned() {
        const TEST: U64 = U64::from_u64(0x0011223344556677);

        let serialized = bincode::serialize(&TEST).unwrap();
        let deserialized: U64 = bincode::deserialize_from(serialized.as_slice()).unwrap();

        assert_eq!(TEST, deserialized);
    }
}
