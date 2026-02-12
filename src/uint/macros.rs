//! Macros used to define traits on aliases of `Uint`.

// TODO(tarcieri): use `generic_const_exprs` when stable to make generic around bits.
macro_rules! impl_uint_aliases {
    ($(($name:ident, $bits:expr, $doc:expr)),+) => {
        $(
            #[doc = $doc]
            #[doc="unsigned big integer."]
            pub type $name = Uint<{ nlimbs($bits) }>;

            impl $crate::traits::EncodedSize for [u8; { nlimbs($bits) * Limb::BYTES }] {
                type Target = EncodedUint<{ nlimbs($bits) }>;
            }

            impl $crate::traits::EncodedSize for EncodedUint<{ nlimbs($bits) }> {
                type Target = [u8; { nlimbs($bits) * Limb::BYTES }];
            }
        )+
     };
}

macro_rules! impl_uint_concat_split_mixed {
    ($name:ident, $size:literal) => {
        impl $crate::traits::Concat<{ U64::LIMBS * $size }> for Uint<{ <$name>::LIMBS - U64::LIMBS * $size }>
        {
            type Output = $name;
        }

        impl $crate::traits::Split<{ U64::LIMBS * $size }> for $name
        {
            type Output = Uint<{ <$name>::LIMBS - U64::LIMBS * $size }>;
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
        impl $crate::traits::Concat<{ <$name>::LIMBS / 2 }> for Uint<{ <$name>::LIMBS / 2 }>
        {
            type Output = $name;
        }

        #[allow(clippy::integer_division_remainder_used, reason = "constant")]
        impl $crate::traits::Split<{ <$name>::LIMBS / 2 }> for $name
        {
            type Output = Uint<{ <$name>::LIMBS / 2 }>;
        }

        #[allow(clippy::integer_division_remainder_used, reason = "constant")]
        impl $crate::traits::SplitEven for $name
        {
            type Output = Uint<{ <$name>::LIMBS / 2 }>;
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
