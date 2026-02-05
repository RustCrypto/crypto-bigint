//! Macros used to define traits on aliases of `Uint`.

// TODO(tarcieri): use `generic_const_exprs` when stable to make generic around bits.
macro_rules! impl_uint_aliases {
    ($(($name:ident, $bits:expr, $doc:expr)),+) => {
        $(
            #[doc = $doc]
            #[doc="unsigned big integer."]
            pub type $name = Uint<{ nlimbs($bits) }>;

            impl MatchSize for EncodedSize<{ nlimbs($bits) * Limb::BYTES }> {
                type Target = EncodedUint<{ nlimbs($bits) }>;
            }

            impl MatchSize for EncodedUint<{ nlimbs($bits) }> {
                type Target = EncodedSize<{ nlimbs($bits) * Limb::BYTES }>;
            }
        )+
     };
}

macro_rules! impl_uint_concat_split_mixed {
    ($name:ident, $size:literal) => {
        impl MatchSize for ConcatSize<{ U64::LIMBS * $size }, { <$name>::LIMBS - U64::LIMBS * $size }> {
            type Target = $name;
        }

        impl MatchSize for SplitSize<{ <$name>::LIMBS }, { U64::LIMBS * $size }> {
            type Target = Uint<{ <$name>::LIMBS - U64::LIMBS * $size }>;
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
        impl MatchSize for ConcatSize<{ <$name>::LIMBS / 2 }, { <$name>::LIMBS / 2 }> {
            type Target = $name;
        }

        #[allow(clippy::integer_division_remainder_used, reason = "constant")]
        impl MatchSize for SplitSize<{ <$name>::LIMBS }, { <$name>::LIMBS / 2 }> {
            type Target = Uint<{ <$name>::LIMBS / 2 }>;
        }

        #[allow(clippy::integer_division_remainder_used, reason = "constant")]
        impl $crate::traits::RemMixed<Uint<{ <$name>::LIMBS / 2 }>> for $name
        {
            fn rem_mixed(&self, reductor: &NonZero<Uint<{ <$name>::LIMBS / 2 }>>) -> Uint<{ <$name>::LIMBS / 2 }> {
                self.div_rem_vartime(reductor).1
            }
        }
    };
    ($($name:ident,)+) => {
        $(
            impl_uint_concat_split_even!($name);
        )+
    }
}
