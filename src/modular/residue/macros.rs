//! Macro support.

/// Implements a modulus with the given name, type, and value, in that specific order. Please
/// `use crypto_bigint::traits::Encoding` to make this work.
///
/// For example,
/// `impl_modulus!(MyModulus, U256, "73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001");`
/// implements a 256-bit modulus named `MyModulus`.
///
/// The modulus _must_ be odd, or this will panic.
// TODO: Use `adt_const_params` once stabilized to make a `Residue` generic around a modulus rather
// than having to implement a ZST + trait
#[macro_export]
macro_rules! impl_modulus {
    ($name:ident, $uint_type:ty, $value:expr) => {
        #[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
        pub struct $name {}
        impl<const DLIMBS: usize> $crate::modular::ResidueParams<{ <$uint_type>::LIMBS }> for $name
        where
            $uint_type: $crate::ConcatMixed<MixedOutput = $crate::Uint<DLIMBS>>,
        {
            const LIMBS: usize = <$uint_type>::LIMBS;
            const MODULUS: $uint_type = {
                let res = <$uint_type>::from_be_hex($value);

                // Check that the modulus is odd
                if res.as_limbs()[0].0 & 1 == 0 {
                    panic!("modulus must be odd");
                }

                res
            };

            // Can unwrap `NonZero::const_new()` here since `MODULUS` was asserted to be non-zero.
            const MODULUS_NZ: $crate::NonZero<$uint_type> =
                $crate::NonZero::<$uint_type>::const_new(Self::MODULUS).0;

            const R: $uint_type = $crate::Uint::MAX
                .rem(&Self::MODULUS_NZ)
                .wrapping_add(&$crate::Uint::ONE);
            const R2: $uint_type = $crate::Uint::rem_wide(Self::R.square_wide(), &Self::MODULUS_NZ);
            const MOD_NEG_INV: $crate::Limb = $crate::Limb(
                $crate::Word::MIN.wrapping_sub(
                    Self::MODULUS
                        .inv_mod2k_vartime($crate::Word::BITS)
                        .0
                        .as_limbs()[0]
                        .0,
                ),
            );
            const R3: $uint_type = $crate::modular::montgomery_reduction(
                &Self::R2.square_wide(),
                &Self::MODULUS,
                Self::MOD_NEG_INV,
            );
        }
    };
}

/// Creates a `Residue` with the given value for a specific modulus.
///
/// For example, `residue!(U256::from(105u64), MyModulus);` creates a `Residue` for 105 mod
/// `MyModulus`.
///
/// The modulus _must_ be odd, or this will panic.
#[macro_export]
macro_rules! const_residue {
    ($variable:ident, $modulus:ident) => {
        $crate::modular::Residue::<$modulus, { $modulus::LIMBS }>::new(&$variable)
    };
}
