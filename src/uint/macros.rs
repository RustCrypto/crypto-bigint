//! Macros used to define traits on aliases of `Uint`.

/// Impl the `Inverter` trait, where we need to compute the number of unsaturated limbs for a given number of bits.
macro_rules! impl_precompute_inverter_trait {
    ($name:ident, $bits:expr) => {
        /// Precompute a Bernstein-Yang inverter using `self` as the modulus.
        impl PrecomputeInverter for Odd<$name> {
            #[allow(trivial_numeric_casts)]
            type Inverter = BernsteinYangInverter<
                { nlimbs!($bits) },
                { bernstein_yang_nlimbs!($bits as usize) },
            >;

            type Output = $name;

            fn precompute_inverter(&self) -> Self::Inverter {
                Self::precompute_inverter_with_adjuster(self, &Uint::ONE)
            }
        }

        /// Precompute a Bernstein-Yang inverter using `self` as the modulus.
        impl PrecomputeInverterWithAdjuster<$name> for Odd<$name> {
            fn precompute_inverter_with_adjuster(&self, adjuster: &$name) -> Self::Inverter {
                Self::Inverter::new(self, adjuster)
            }
        }
    };
}

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

            impl_precompute_inverter_trait!($name, $bits);
        )+
     };
}

macro_rules! impl_uint_concat_split_mixed {
    ($name:ident, $size:literal) => {
        impl $crate::traits::ConcatMixed<Uint<{ U64::LIMBS * $size }>> for Uint<{ <$name>::LIMBS - U64::LIMBS * $size }>
        {
            type MixedOutput = $name;

            fn concat_mixed(&self, lo: &Uint<{ U64::LIMBS * $size }>) -> Self::MixedOutput {
                $crate::uint::concat::concat_mixed(lo, self)
            }
        }

        impl $crate::traits::SplitMixed<Uint<{ U64::LIMBS * $size }>, Uint<{ <$name>::LIMBS - U64::LIMBS * $size }>> for $name
        {
            fn split_mixed(&self) -> (Uint<{ U64::LIMBS * $size }>, Uint<{ <$name>::LIMBS - U64::LIMBS * $size }>) {
                $crate::uint::split::split_mixed(self)
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
        impl $crate::traits::ConcatMixed<Uint<{ <$name>::LIMBS / 2 }>> for Uint<{ <$name>::LIMBS / 2 }>
        {
            type MixedOutput = $name;

            fn concat_mixed(&self, lo: &Uint<{ <$name>::LIMBS / 2 }>) -> Self::MixedOutput {
                $crate::uint::concat::concat_mixed(lo, self)
            }
        }

        impl Uint<{ <$name>::LIMBS / 2 }> {
            /// Concatenate the two values, with `self` as most significant and `rhs`
            /// as the least significant.
            pub const fn concat(&self, lo: &Uint<{ <$name>::LIMBS / 2 }>) -> $name {
                $crate::uint::concat::concat_mixed(lo, self)
            }
        }

        impl $crate::traits::SplitMixed<Uint<{ <$name>::LIMBS / 2 }>, Uint<{ <$name>::LIMBS / 2 }>> for $name
        {
            fn split_mixed(&self) -> (Uint<{ <$name>::LIMBS / 2 }>, Uint<{ <$name>::LIMBS / 2 }>) {
                $crate::uint::split::split_mixed(self)
            }
        }

        impl $crate::traits::Split for $name
        {
            type Output = Uint<{ <$name>::LIMBS / 2 }>;
        }

        impl $name {
            /// Split this number in half, returning its high and low components
            /// respectively.
            pub const fn split(&self) -> (Uint<{ <$name>::LIMBS / 2 }>, Uint<{ <$name>::LIMBS / 2 }>) {
                $crate::uint::split::split_mixed(self)
            }
        }
    };
    ($($name:ident,)+) => {
        $(
            impl_uint_concat_split_even!($name);
        )+
    }
}
