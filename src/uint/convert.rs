macro_rules! impl_convert {
    (($source_type:ident, $source_bits:expr), ($(($target_type:ident, $target_bits:expr)),+ $(,)?)) => {
        impl $source_type {
            $(
                paste::paste! {
                    pub fn [<to_ $target_type:lower>](&self) -> $target_type {
                        let mut limbs = [Limb::ZERO; nlimbs!($target_bits)];
                        let mut i = 0;

                        while i < nlimbs!($source_bits) {
                            limbs[i] = self.limbs[i];
                            i += 1;
                        }

                        Uint { limbs }
                    }
                }
            )+
        }
    };
}

#[cfg(test)]
mod tests {
    use crate::{U128, U384, U64};

    #[test]
    fn concat_zero_equals_convert() {
        let x = U64::from_u64(0x0011223344556677);

        assert_eq!(U64::ZERO.concat(&x), U128::from_u64(0x0011223344556677));
    }

    #[test]
    fn converts_non_concatable_types() {
        assert_eq!(U384::ONE, U128::ONE.to_u384());
    }
}
