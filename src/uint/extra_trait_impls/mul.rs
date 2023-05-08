use crate::{
    Uint, U1024, U128, U1280, U1536, U1792, U192, U2048, U256, U3072, U320, U3584, U384, U4096,
    U448, U512, U576, U6144, U64, U640, U768, U8192, U896,
};

use core::ops::Mul;

macro_rules! impl_mul_cross_sizes {
    (($first_type:ident, $first_bits:expr), ($(($second_type:ident, $second_bits:expr)),+ $(,)?)) => {
        $(
            impl Mul<$second_type> for $first_type {
                type Output = Uint<{nlimbs!($first_bits) + nlimbs!($second_bits)}>;

                fn mul(self, rhs: $second_type) -> Uint<{nlimbs!($first_bits) + nlimbs!($second_bits)}> {
                    self.mul_wide(&rhs).into()
                }
            }

            impl Mul<&$second_type> for $first_type  {
                type Output = Uint<{nlimbs!($first_bits) + nlimbs!($second_bits)}>;

                fn mul(self, rhs: &$second_type) -> Uint<{nlimbs!($first_bits) + nlimbs!($second_bits)}> {
                    self.mul_wide(rhs).into()
                }
            }

            impl Mul<$second_type> for &$first_type  {
                type Output = Uint<{nlimbs!($first_bits) + nlimbs!($second_bits)}>;

                fn mul(self, rhs: $second_type) -> Uint<{nlimbs!($first_bits) + nlimbs!($second_bits)}> {
                    self.mul_wide(&rhs).into()
                }
            }

            impl Mul<&$second_type> for &$first_type {
                type Output = Uint<{nlimbs!($first_bits) + nlimbs!($second_bits)}>;

                fn mul(self, rhs: &$second_type) -> Uint<{nlimbs!($first_bits) + nlimbs!($second_bits)}> {
                    self.mul_wide(rhs).into()
                }
            }

            impl Mul<$first_type> for $second_type {
                type Output = Uint<{nlimbs!($second_bits) + nlimbs!($first_bits)}>;

                fn mul(self, rhs: $first_type) -> Uint<{nlimbs!($second_bits) + nlimbs!($first_bits)}> {
                    self.mul_wide(&rhs).into()
                }
            }

            impl Mul<&$first_type> for $second_type  {
                type Output = Uint<{nlimbs!($second_bits) + nlimbs!($first_bits)}>;

                fn mul(self, rhs: &$first_type) -> Uint<{nlimbs!($second_bits) + nlimbs!($first_bits)}> {
                    self.mul_wide(rhs).into()
                }
            }

            impl Mul<$first_type> for &$second_type  {
                type Output = Uint<{nlimbs!($second_bits) + nlimbs!($first_bits)}>;

                fn mul(self, rhs: $first_type) -> Uint<{nlimbs!($second_bits) + nlimbs!($first_bits)}> {
                    self.mul_wide(&rhs).into()
                }
            }

            impl Mul<&$first_type> for &$second_type {
                type Output = Uint<{nlimbs!($second_bits) + nlimbs!($first_bits)}>;

                fn mul(self, rhs: &$first_type) -> Uint<{nlimbs!($second_bits) + nlimbs!($first_bits)}> {
                    self.mul_wide(rhs).into()
                }
            }
        )+
    };
}

impl_mul_cross_sizes! {
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

impl_mul_cross_sizes! {
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

impl_mul_cross_sizes! {
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

impl_mul_cross_sizes! {
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

impl_mul_cross_sizes! {
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

impl_mul_cross_sizes! {
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

impl_mul_cross_sizes! {
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

impl_mul_cross_sizes! {
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

impl_mul_cross_sizes! {
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

impl_mul_cross_sizes! {
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

impl_mul_cross_sizes! {
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

impl_mul_cross_sizes! {
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

impl_mul_cross_sizes! {
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

impl_mul_cross_sizes! {
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

impl_mul_cross_sizes! {
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

impl_mul_cross_sizes! {
    (U2048, 2048),
    (
        (U3072, 3072),
        (U3584, 3584),
        (U4096, 4096),
        (U6144, 6144),
        (U8192, 8192)
    )
}

impl_mul_cross_sizes! {
    (U3072, 3072),
    (
        (U3584, 3584),
        (U4096, 4096),
        (U6144, 6144),
        (U8192, 8192)
    )
}

impl_mul_cross_sizes! {
    (U3584, 3584),
    (
        (U4096, 4096),
        (U6144, 6144),
        (U8192, 8192)
    )
}

impl_mul_cross_sizes! {
    (U4096, 4096),
    (
        (U6144, 6144),
        (U8192, 8192)
    )
}

impl_mul_cross_sizes! {
    (U6144, 6144),
    (
        (U8192, 8192)
    )
}

#[cfg(test)]
mod tests {
    use crate::{U128, U256, U384};

    #[test]
    fn mul_wide_zero_and_one_cross_sizes() {
        assert_eq!(U128::ZERO.mul_wide(&U256::ZERO), (U256::ZERO, U128::ZERO));
        assert_eq!(U128::ZERO.mul_wide(&U256::ONE), (U256::ZERO, U128::ZERO));
        assert_eq!(U128::ONE.mul_wide(&U256::ZERO), (U256::ZERO, U128::ZERO));
        assert_eq!(U128::ONE.mul_wide(&U256::ONE), (U256::ONE, U128::ZERO));
    }

    #[test]
    fn mul_wide_cross_sizes() {
        let x = U128::from_be_hex("ffffffffffffffffffffffffffffffff");
        let y =
            U256::from_be_hex("0fffffffffffffffffffffafffffffffffffffffffffffffffffffffffffffff");
        let (lo, hi) = x.mul_wide(&y);

        assert_eq!(
            lo,
            U256::from_be_hex("f0000000000000000000004fffffffff00000000000000000000000000000001")
        );

        assert_eq!(hi, U128::from_be_hex("0fffffffffffffffffffffafffffffff"));
    }

    #[test]
    fn mul_cross_sizes() {
        let x = U128::from_be_hex("ffffffffffffffffffffffffffffffff");
        let y =
            U256::from_be_hex("0fffffffffffffffffffffafffffffffffffffffffffffffffffffffffffffff");
        let xy: U384 = x.mul_wide(&y).into();

        assert_eq!(xy, x * y);
        assert_eq!(xy, y * x);

        assert_eq!(
            xy,
            U384::from_be_hex("0fffffffffffffffffffffaffffffffff0000000000000000000004fffffffff00000000000000000000000000000001")
        );
    }
}
