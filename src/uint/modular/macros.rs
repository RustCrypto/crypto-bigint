// TODO: Use `adt_const_params` once stabilized to make a `Residue` generic around a modulus rather than having to implement a ZST + trait
macro_rules! impl_modulus {
    ($name:ident, $uint_type:ty, $value:expr) => {
        use crate::traits::{Encoding, Concat, Split};
        use crate::{Limb, Word};

        #[derive(Clone, Copy)]
        pub struct $name {}
        impl<const DLIMBS: usize> ResidueParams<{nlimbs!(<$uint_type>::BIT_SIZE)}> for $name
        where
            UInt<4>: Concat<Output = UInt<DLIMBS>>,
            UInt<DLIMBS>: Split<Output = $uint_type>,
        {
            const MODULUS: UInt<{nlimbs!(<$uint_type>::BIT_SIZE)}> = <$uint_type>::from_be_hex($value);
            const R: UInt<{nlimbs!(<$uint_type>::BIT_SIZE)}> = UInt::MAX.ct_reduce(&Self::MODULUS).0.wrapping_add(&UInt::ONE);
            const R2: UInt<{nlimbs!(<$uint_type>::BIT_SIZE)}> = UInt::ct_reduce_wide(Self::R.square_wide(), &Self::MODULUS).0;
            const MOD_NEG_INV: Limb = Limb(Word::MIN.wrapping_sub(Self::MODULUS.inv_mod2k(Word::BITS as usize).limbs[0].0));
        }
     };
}
