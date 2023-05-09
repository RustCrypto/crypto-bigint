use crate::{
    Uint, U1024, U128, U1280, U1536, U1792, U192, U2048, U256, U3072, U320, U3584, U384, U4096,
    U448, U512, U576, U6144, U64, U640, U768, U8192, U896,
};

use crate::{Concat, Limb};

macro_rules! impl_concat_cross_sizes {
    (($first_type:ident, $first_bits:expr), ($(($second_type:ident, $second_bits:expr)),+ $(,)?)) => {
        $(
            impl Concat<$second_type> for $first_type {
                type Output = Uint<{nlimbs!($first_bits) + nlimbs!($second_bits)}>;

                fn concat(&self, rhs: &$second_type) -> Self::Output {
                    concat_internal!(self, $first_bits, rhs, $second_bits)
                }
            }

            impl From<($first_type, $second_type)> for Uint<{nlimbs!($first_bits) + nlimbs!($second_bits)}> {
                fn from(nums: ($first_type, $second_type)) -> Uint<{nlimbs!($first_bits) + nlimbs!($second_bits)}> {
                    <$second_type as Concat<$first_type>>::concat(&nums.1, &nums.0)
                }
            }

            impl Concat<$first_type> for $second_type {
                type Output = Uint<{nlimbs!($second_bits) + nlimbs!($first_bits)}>;

                fn concat(&self, rhs: &$first_type) -> Self::Output {
                    concat_internal!(self, $second_bits, rhs, $first_bits)
                }
            }

            impl From<($second_type, $first_type)> for Uint<{nlimbs!($second_bits) + nlimbs!($first_bits)}> {
                fn from(nums: ($second_type, $first_type)) -> Uint<{nlimbs!($second_bits) + nlimbs!($first_bits)}> {
                    <$first_type as Concat<$second_type>>::concat(&nums.1, &nums.0)
                }
            }
        )+
    };
}

impl_concat_cross_sizes! {
    (U64, 64),
    (
    (U128, 128),
    (U192, 192),
    (U256, 256),
    (U320, 320),
    (U384, 384),
    (U448, 448),
    (U512, 512),
    (U576, 576),
    (U640, 640),
    (U768, 768),
    (U896, 896),
    (U1024, 1024),
    (U1280, 1280),
    (U1536, 1536),
    (U1792, 1792),
    (U2048, 2048),
    (U3072, 3072),
    (U3584, 3584),
    (U4096, 4096),
    (U6144, 6144),
    (U8192, 8192)
    )
}

impl_concat_cross_sizes! {
    (U128, 128),
    (
        (U192, 192),
        (U256, 256),
        (U320, 320),
        (U384, 384),
        (U448, 448),
        (U512, 512),
        (U576, 576),
        (U640, 640),
        (U768, 768),
        (U896, 896),
        (U1024, 1024),
        (U1280, 1280),
        (U1536, 1536),
        (U1792, 1792),
        (U2048, 2048),
        (U3072, 3072),
        (U3584, 3584),
        (U4096, 4096),
        (U6144, 6144),
        (U8192, 8192)
    )
}

impl_concat_cross_sizes! {
    (U192, 192),
    (
        (U256, 256),
        (U320, 320),
        (U384, 384),
        (U448, 448),
        (U512, 512),
        (U576, 576),
        (U640, 640),
        (U768, 768),
        (U896, 896),
        (U1024, 1024),
        (U1280, 1280),
        (U1536, 1536),
        (U1792, 1792),
        (U2048, 2048),
        (U3072, 3072),
        (U3584, 3584),
        (U4096, 4096),
        (U6144, 6144),
        (U8192, 8192)
    )
}

impl_concat_cross_sizes! {
    (U256, 256),
    (
        (U320, 320),
        (U384, 384),
        (U448, 448),
        (U512, 512),
        (U576, 576),
        (U640, 640),
        (U768, 768),
        (U896, 896),
        (U1024, 1024),
        (U1280, 1280),
        (U1536, 1536),
        (U1792, 1792),
        (U2048, 2048),
        (U3072, 3072),
        (U3584, 3584),
        (U4096, 4096),
        (U6144, 6144),
        (U8192, 8192)
    )
}

impl_concat_cross_sizes! {
    (U320, 320),
    (
        (U384, 384),
        (U448, 448),
        (U512, 512),
        (U576, 576),
        (U640, 640),
        (U768, 768),
        (U896, 896),
        (U1024, 1024),
        (U1280, 1280),
        (U1536, 1536),
        (U1792, 1792),
        (U2048, 2048),
        (U3072, 3072),
        (U3584, 3584),
        (U4096, 4096),
        (U6144, 6144),
        (U8192, 8192)
    )
}

impl_concat_cross_sizes! {
    (U384, 384),
    (
        (U448, 448),
        (U512, 512),
        (U576, 576),
        (U640, 640),
        (U768, 768),
        (U896, 896),
        (U1024, 1024),
        (U1280, 1280),
        (U1536, 1536),
        (U1792, 1792),
        (U2048, 2048),
        (U3072, 3072),
        (U3584, 3584),
        (U4096, 4096),
        (U6144, 6144),
        (U8192, 8192)
    )
}

impl_concat_cross_sizes! {
    (U448, 448),
    (
        (U512, 512),
        (U576, 576),
        (U640, 640),
        (U768, 768),
        (U896, 896),
        (U1024, 1024),
        (U1280, 1280),
        (U1536, 1536),
        (U1792, 1792),
        (U2048, 2048),
        (U3072, 3072),
        (U3584, 3584),
        (U4096, 4096),
        (U6144, 6144),
        (U8192, 8192)
    )
}

impl_concat_cross_sizes! {
    (U512, 512),
    (
        (U576, 576),
        (U640, 640),
        (U768, 768),
        (U896, 896),
        (U1024, 1024),
        (U1280, 1280),
        (U1536, 1536),
        (U1792, 1792),
        (U2048, 2048),
        (U3072, 3072),
        (U3584, 3584),
        (U4096, 4096),
        (U6144, 6144),
        (U8192, 8192)
    )
}

impl_concat_cross_sizes! {
    (U576, 576),
    (
        (U640, 640),
        (U768, 768),
        (U896, 896),
        (U1024, 1024),
        (U1280, 1280),
        (U1536, 1536),
        (U1792, 1792),
        (U2048, 2048),
        (U3072, 3072),
        (U3584, 3584),
        (U4096, 4096),
        (U6144, 6144),
        (U8192, 8192)
    )
}

impl_concat_cross_sizes! {
    (U640, 640),
    (
        (U768, 768),
        (U896, 896),
        (U1024, 1024),
        (U1280, 1280),
        (U1536, 1536),
        (U1792, 1792),
        (U2048, 2048),
        (U3072, 3072),
        (U3584, 3584),
        (U4096, 4096),
        (U6144, 6144),
        (U8192, 8192)
    )
}

impl_concat_cross_sizes! {
    (U768, 768),
    (
        (U896, 896),
        (U1024, 1024),
        (U1280, 1280),
        (U1536, 1536),
        (U1792, 1792),
        (U2048, 2048),
        (U3072, 3072),
        (U3584, 3584),
        (U4096, 4096),
        (U6144, 6144),
        (U8192, 8192)
    )
}

impl_concat_cross_sizes! {
    (U896, 896),
    (
        (U1024, 1024),
        (U1280, 1280),
        (U1536, 1536),
        (U1792, 1792),
        (U2048, 2048),
        (U3072, 3072),
        (U3584, 3584),
        (U4096, 4096),
        (U6144, 6144),
        (U8192, 8192)
    )
}

impl_concat_cross_sizes! {
    (U1024, 1024),
    (
        (U1280, 1280),
        (U1536, 1536),
        (U1792, 1792),
        (U2048, 2048),
        (U3072, 3072),
        (U3584, 3584),
        (U4096, 4096),
        (U6144, 6144),
        (U8192, 8192)
    )
}

impl_concat_cross_sizes! {
    (U1280, 1280),
    (
        (U1536, 1536),
        (U1792, 1792),
        (U2048, 2048),
        (U3072, 3072),
        (U3584, 3584),
        (U4096, 4096),
        (U6144, 6144),
        (U8192, 8192)
    )
}

impl_concat_cross_sizes! {
    (U1536, 1536),
    (
        (U1792, 1792),
        (U2048, 2048),
        (U3072, 3072),
        (U3584, 3584),
        (U4096, 4096),
        (U6144, 6144),
        (U8192, 8192)
    )
}

impl_concat_cross_sizes! {
    (U2048, 2048),
    (
        (U3072, 3072),
        (U3584, 3584),
        (U4096, 4096),
        (U6144, 6144),
        (U8192, 8192)
    )
}

impl_concat_cross_sizes! {
    (U3072, 3072),
    (
        (U3584, 3584),
        (U4096, 4096),
        (U6144, 6144),
        (U8192, 8192)
    )
}

impl_concat_cross_sizes! {
    (U3584, 3584),
    (
        (U4096, 4096),
        (U6144, 6144),
        (U8192, 8192)
    )
}

impl_concat_cross_sizes! {
    (U4096, 4096),
    (
        (U6144, 6144),
        (U8192, 8192)
    )
}

impl_concat_cross_sizes! {
    (U6144, 6144),
    (
        (U8192, 8192)
    )
}

#[cfg(test)]
mod tests {
    use crate::{Concat, U128, U192, U64};

    #[test]
    fn concat_other() {
        let x = U64::from_u64(0x0011223344556677);
        let y = U128::from_be_hex("00112233445566778899aabbccddeeff");

        assert_eq!(
            <U64 as Concat<U128>>::concat(&x, &y),
            U192::from_be_hex("001122334455667700112233445566778899aabbccddeeff")
        );

        assert_eq!(
            <U128 as Concat<U64>>::concat(&y, &x),
            U192::from_be_hex("00112233445566778899aabbccddeeff0011223344556677")
        );
    }

    #[test]
    fn convert_cross_sizes() {
        let res: U192 = U64::ONE.mul_wide(&U128::ONE).into();
        assert_eq!(res, U192::ONE);
    }
}
