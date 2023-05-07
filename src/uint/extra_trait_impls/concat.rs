macro_rules! impl_concat_cross_sizes {
    (($first_type:ident, $first_bits:expr), ($(($second_type:ident, $second_bits:expr)),+ $(,)?)) => {
        $(
            impl Concat<$second_type> for $first_type {
                type Output = Uint<{nlimbs!($first_bits) + nlimbs!($second_bits)}>;

                fn concat(&self, rhs: &$second_type) -> Self::Output {
                    let mut limbs = [Limb::ZERO; nlimbs!($first_bits) + nlimbs!($second_bits)];
                    let mut i = 0;
                    let mut j = 0;

                    while j < nlimbs!($second_bits) {
                        limbs[i] = rhs.limbs[j];
                        i += 1;
                        j += 1;
                    }

                    j = 0;
                    while j < nlimbs!($first_bits) {
                        limbs[i] = self.limbs[j];
                        i += 1;
                        j += 1;
                    }

                    Uint { limbs }
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
                    let mut limbs = [Limb::ZERO; nlimbs!($second_bits) + nlimbs!($first_bits)];
                    let mut i = 0;
                    let mut j = 0;

                    while j < nlimbs!($first_bits) {
                        limbs[i] = rhs.limbs[j];
                        i += 1;
                        j += 1;
                    }

                    j = 0;
                    while j < nlimbs!($second_bits) {
                        limbs[i] = self.limbs[j];
                        i += 1;
                        j += 1;
                    }

                    Uint { limbs }
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
    (U256, 256),
    (U384, 384),
    (U512, 512),
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
        (U256, 256),
        (U384, 384),
        (U512, 512),
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
        (U384, 384),
        (U512, 512),
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
        (U512, 512),
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
        let hi = U64::from_u64(0x0011223344556677);
        let lo = U128::from_be_hex("00112233445566778899aabbccddeeff");

        assert_eq!(
            <U64 as Concat<U128>>::concat(&hi, &lo),
            U192::from_be_hex("001122334455667700112233445566778899aabbccddeeff")
        );

        let hi = U128::from_be_hex("00112233445566778899aabbccddeeff");
        let lo = U64::from_u64(0x0011223344556677);

        assert_eq!(
            <U128 as Concat<U64>>::concat(&hi, &lo),
            U192::from_be_hex("00112233445566778899aabbccddeeff0011223344556677")
        );
    }
}
