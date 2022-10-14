// TODO: Use `adt_const_params` once stabilized to make a `Residue` generic around a modulus rather than having to implement a ZST + trait
#[macro_export]
macro_rules! impl_modulus {
    ($name:ident, $uint_type:ty, $value:expr) => {
        // use $crate::traits::{Encoding, Concat, Split};
        // use $crate::{Limb, Word};

        #[derive(Clone, Copy, PartialEq, Eq, Debug)]
        pub struct $name {}
        impl<const DLIMBS: usize> ResidueParams<{ nlimbs!(<$uint_type>::BIT_SIZE) }> for $name
        where
            $crate::UInt<{ nlimbs!(<$uint_type>::BIT_SIZE) }>:
                $crate::traits::Concat<Output = $crate::UInt<DLIMBS>>,
            $crate::UInt<DLIMBS>: $crate::traits::Split<Output = $uint_type>,
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
            const MOD_NEG_INV: $crate::Limb = $crate::Limb(
                $crate::Word::MIN
                    .wrapping_sub(Self::MODULUS.inv_mod2k($crate::Word::BITS as usize).limbs[0].0),
            );
        }
    };
}

#[macro_export]
macro_rules! residue {
    ($variable:ident, $modulus:ident) => {
        $crate::uint::modular::Residue::<$modulus, { $modulus::LIMBS }>::new($variable)
    };
}
