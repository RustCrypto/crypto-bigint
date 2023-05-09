macro_rules! convert_internal {
    ($x:ident, $source_bits:expr, $target_bits:expr) => {{
        let mut limbs = [Limb::ZERO; nlimbs!($target_bits)];
        let mut i = 0;

        while i < nlimbs!($source_bits) {
            limbs[i] = $x.limbs[i];
            i += 1;
        }

        Uint { limbs }
    }};
}

macro_rules! impl_convert {
    ($source_type:ident, $source_bits:expr, $target_type:ident, $target_bits:expr) => {
        impl From<$source_type> for $target_type {
            fn from(x: $source_type) -> Self {
                convert_internal!(x, $source_bits, $target_bits)
            }
        }

        impl From<&$source_type> for $target_type {
            fn from(x: &$source_type) -> Self {
                convert_internal!(x, $source_bits, $target_bits)
            }
        }
    };
}

#[cfg(test)]
mod tests {
    use crate::{U128, U384, U64};

    #[test]
    fn concat_zero_equals_convert() {
        let x = U64::from_u64(0x0011223344556677);

        assert_eq!(U128::from(&x), U128::from_u64(0x0011223344556677));
        assert_eq!(U128::from(x), U128::from_u64(0x0011223344556677));
    }

    #[test]
    fn converts_non_concatable_types() {
        assert_eq!(U384::ONE, U384::from(&U128::ONE));
        assert_eq!(U384::ONE, U384::from(U128::ONE));
    }
}
