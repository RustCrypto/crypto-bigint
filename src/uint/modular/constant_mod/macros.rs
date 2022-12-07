// TODO: Use `adt_const_params` once stabilized to make a `Residue` generic around a modulus rather than having to implement a ZST + trait
#[macro_export]
/// Implements a modulus with the given name, type, and value, in that specific order. Please `use crypto_bigint::traits::Encoding` to make this work.
/// For example, `impl_modulus!(MyModulus, U256, "73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001");` implements a 256-bit modulus named `MyModulus`.
macro_rules! impl_modulus {
    ($name:ident, $uint_type:ty, $value:expr) => {
        #[derive(Clone, Copy, Default, PartialEq, Eq, Debug)]
        pub struct $name {}
        impl<const DLIMBS: usize> ResidueParams<{ nlimbs!(<$uint_type>::BIT_SIZE) }> for $name
        where
            $crate::UInt<{ nlimbs!(<$uint_type>::BIT_SIZE) }>:
                $crate::Concat<Output = $crate::UInt<DLIMBS>>,
        {
            const LIMBS: usize = { nlimbs!(<$uint_type>::BIT_SIZE) };
            const MODULUS: $crate::UInt<{ nlimbs!(<$uint_type>::BIT_SIZE) }> =
                <$uint_type>::from_be_hex($value);
            const R: $crate::UInt<{ nlimbs!(<$uint_type>::BIT_SIZE) }> = $crate::UInt::MAX
                .ct_reduce(&Self::MODULUS)
                .0
                .wrapping_add(&$crate::UInt::ONE);
            const R2: $crate::UInt<{ nlimbs!(<$uint_type>::BIT_SIZE) }> =
                $crate::UInt::ct_reduce_wide(Self::R.square_wide(), &Self::MODULUS).0;
            const MOD_NEG_INV: $crate::Limb =
                $crate::Limb($crate::Word::MIN.wrapping_sub(
                    Self::MODULUS.inv_mod2k($crate::Word::BITS as usize).limbs()[0].0,
                ));
            const R3: $crate::UInt<{ nlimbs!(<$uint_type>::BIT_SIZE) }> =
                $crate::modular::reduction::montgomery_reduction(
                    Self::R2.square_wide(),
                    Self::MODULUS,
                    Self::MOD_NEG_INV,
                );
        }
    };
}

#[macro_export]
/// Creates a `Residue` with the given value for a specific modulus.
/// For example, `residue!(U256::from(105u64), MyModulus);` creates a `Residue` for 105 mod `MyModulus`.
macro_rules! const_residue {
    ($variable:ident, $modulus:ident) => {
        $crate::uint::modular::constant_mod::Residue::<$modulus, { $modulus::LIMBS }>::new(
            $variable,
        )
    };
}
