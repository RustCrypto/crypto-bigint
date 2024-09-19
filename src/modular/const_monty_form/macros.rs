//! Macro support.

/// Implements a modulus with the given name, type, and value, in that specific order. Please
/// `use crypto_bigint::traits::Encoding` to make this work.
///
/// For example,
/// `impl_modulus!(MyModulus, U256, "73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001");`
/// implements a 256-bit modulus named `MyModulus`.
///
/// The modulus _must_ be odd, or this will panic.
// TODO: Use `adt_const_params` once stabilized to make a `ConstMontyForm` generic around a modulus rather
// than having to implement a ZST + trait
#[macro_export]
macro_rules! impl_modulus {
    ($name:ident, $uint_type:ty, $value:expr) => {
        impl_modulus!(
            $name,
            $uint_type,
            $value,
            "Modulus which impls `ConstMontyParams`"
        );
    };
    ($name:ident, $uint_type:ty, $value:expr, $doc:expr) => {
        #[doc = $doc]
        #[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
        pub struct $name;
        impl<const DLIMBS: usize> $crate::modular::ConstMontyParams<{ <$uint_type>::LIMBS }>
            for $name
        where
            $uint_type: $crate::ConcatMixed<MixedOutput = $crate::Uint<DLIMBS>>,
        {
            const LIMBS: usize = <$uint_type>::LIMBS;
            const MODULUS: $crate::Odd<$uint_type> = $crate::Odd::<$uint_type>::from_be_hex($value);

            // `R mod MODULUS` where `R = 2^BITS`.
            // Represents 1 in Montgomery form.
            const ONE: $uint_type = $crate::Uint::MAX
                .rem_vartime(Self::MODULUS.as_nz_ref())
                .wrapping_add(&$crate::Uint::ONE);

            // `R^2 mod MODULUS`, used to convert integers to Montgomery form.
            const R2: $uint_type =
                $crate::Uint::rem_wide_vartime(Self::ONE.square_wide(), Self::MODULUS.as_nz_ref());

            const MOD_NEG_INV: $crate::Limb = $crate::Limb(
                $crate::Word::MIN.wrapping_sub(
                    Self::MODULUS
                        .as_ref()
                        .inv_mod2k_vartime($crate::Word::BITS)
                        .expect("modulus ensured odd")
                        .as_limbs()[0]
                        .0,
                ),
            );

            // Leading zeros in the modulus, used to choose optimized algorithms.
            const MOD_LEADING_ZEROS: u32 = {
                let z = Self::MODULUS.as_ref().leading_zeros();
                if z >= $crate::Word::BITS {
                    $crate::Word::BITS - 1
                } else {
                    z
                }
            };

            const R3: $uint_type = $crate::modular::montgomery_reduction(
                &Self::R2.square_wide(),
                &Self::MODULUS,
                Self::MOD_NEG_INV,
            );
        }
    };
}

/// Creates a `ConstMontyForm` with the given value for a specific modulus.
///
/// For example, `const_monty_form!(U256::from(105u64), MyModulus);`
/// creates a `ConstMontyForm` for 105 mod `MyModulus`.
///
/// The modulus _must_ be odd, or this will panic.
#[macro_export]
macro_rules! const_monty_form {
    ($variable:ident, $modulus:ident) => {
        $crate::modular::ConstMontyForm::<$modulus, { $modulus::LIMBS }>::new(&$variable)
    };
}
