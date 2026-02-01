//! Macros used to define traits on aliases of `Uint`.

// TODO(tarcieri): use `generic_const_exprs` when stable to make generic around bits.
macro_rules! impl_uint_aliases {
    ($(($name:ident, $bits:expr, $doc:expr)),+) => {
        $(
            #[doc = $doc]
            #[doc="unsigned big integer."]
            pub type $name = Uint<{ nlimbs!($bits) }>;

            impl From<EncodedUint<{ nlimbs!($bits) }>> for [u8; { nlimbs!($bits) * Limb::BYTES }] {
                #[inline]
                fn from(input: EncodedUint<{ nlimbs!($bits) }>) -> Self {
                    let mut output = [0u8; nlimbs!($bits) * Limb::BYTES];
                    output.as_mut_slice().copy_from_slice(input.as_ref());
                    output
                }
            }

            impl From<[u8; { nlimbs!($bits) * Limb::BYTES }]> for EncodedUint< { nlimbs!($bits) }> {
                #[inline]
                fn from(input: [u8; { nlimbs!($bits) * Limb::BYTES }]) -> Self {
                    let mut output = Self::default();
                    output.as_mut().copy_from_slice(input.as_ref());
                    output
                }
            }
        )+
     };
}

macro_rules! impl_uint_concat_split_mixed {
    ($name:ident, $size:literal) => {
        impl $crate::traits::ConcatMixed<Uint<{ U64::LIMBS * $size }>> for Uint<{ <$name>::LIMBS - U64::LIMBS * $size }>
        {
            type MixedOutput = $name;

            fn concat_mixed(&self, hi: &Uint<{ U64::LIMBS * $size }>) -> Self::MixedOutput {
                Uint::concat_mixed(self, hi)
            }
        }

        impl $crate::traits::SplitMixed<Uint<{ U64::LIMBS * $size }>, Uint<{ <$name>::LIMBS - U64::LIMBS * $size }>> for $name
        {
            fn split_mixed(&self) -> (Uint<{ U64::LIMBS * $size }>, Uint<{ <$name>::LIMBS - U64::LIMBS * $size }>) {
                self.split_mixed()
            }
        }

        impl $crate::traits::RemMixed<Uint<{ U64::LIMBS * $size }>> for $name
        {
            fn rem_mixed(&self, reductor: &NonZero<Uint<{ U64::LIMBS * $size }>>) -> Uint<{ U64::LIMBS * $size }> {
                self.div_rem_vartime(reductor).1
            }
        }
    };
    ($name:ident, [ $($size:literal),+ ]) => {
        $(
            impl_uint_concat_split_mixed!($name, $size);
        )+
    };
    ($( ($name:ident, $sizes:tt), )+) => {
        $(
            impl_uint_concat_split_mixed!($name, $sizes);
        )+
    };
}

macro_rules! impl_uint_concat_split_even {
    ($name:ident) => {
        #[allow(clippy::integer_division_remainder_used, reason = "constant")]
        impl $crate::traits::ConcatMixed<Uint<{ <$name>::LIMBS / 2 }>> for Uint<{ <$name>::LIMBS / 2 }>
        {
            type MixedOutput = $name;

            fn concat_mixed(&self, hi: &Uint<{ <$name>::LIMBS / 2 }>) -> Self::MixedOutput {
                Uint::concat_mixed(self, hi)
            }
        }

        #[allow(clippy::integer_division_remainder_used, reason = "constant")]
        impl $crate::traits::SplitMixed<Uint<{ <$name>::LIMBS / 2 }>, Uint<{ <$name>::LIMBS / 2 }>> for $name
        {
            fn split_mixed(&self) -> (Uint<{ <$name>::LIMBS / 2 }>, Uint<{ <$name>::LIMBS / 2 }>) {
                self.split_mixed()
            }
        }

        #[allow(clippy::integer_division_remainder_used, reason = "constant")]
        impl $crate::traits::RemMixed<Uint<{ <$name>::LIMBS / 2 }>> for $name
        {
            fn rem_mixed(&self, reductor: &NonZero<Uint<{ <$name>::LIMBS / 2 }>>) -> Uint<{ <$name>::LIMBS / 2 }> {
                self.div_rem_vartime(reductor).1
            }
        }

        #[allow(clippy::integer_division_remainder_used, reason = "constant")]
        impl $crate::traits::Split for $name
        {
            type Output = Uint<{ <$name>::LIMBS / 2 }>;
        }
    };
    ($($name:ident,)+) => {
        $(
            impl_uint_concat_split_even!($name);
        )+
    }
}
