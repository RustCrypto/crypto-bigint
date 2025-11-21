//! Macros used to define traits on aliases of `Uint`.

// TODO(tarcieri): use `generic_const_exprs` when stable to make generic around bits.
macro_rules! impl_uint_aliases {
    ($(($name:ident, $bits:expr, $doc:expr)),+) => {
        $(
            #[doc = $doc]
            #[doc="unsigned big integer."]
            pub type $name = Uint<{ nlimbs!($bits) }>;

            impl $name {
                /// Serialize as big endian bytes.
                pub const fn to_be_bytes(&self) -> [u8; $bits / 8] {
                    encoding::uint_to_be_bytes::<{ nlimbs!($bits) }, { $bits / 8 }>(self)
                }

                /// Serialize as little endian bytes.
                pub const fn to_le_bytes(&self) -> [u8; $bits / 8] {
                    encoding::uint_to_le_bytes::<{ nlimbs!($bits) }, { $bits / 8 }>(self)
                }
            }

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
                    encoding::uint_to_be_bytes(self)
                }

                #[inline]
                fn to_le_bytes(&self) -> Self::Repr {
                    encoding::uint_to_le_bytes(self)
                }
            }
        )+
     };
}
