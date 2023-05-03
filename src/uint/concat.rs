// TODO(tarcieri): use `const_evaluatable_checked` when stable to make generic around bits.
macro_rules! impl_concat {
    ($(($name:ident, $bits:expr)),+) => {
        $(
            impl $name {
                /// Concatenate the two values, with `self` as most significant and `rhs`
                /// as the least significant.
                pub const fn concat(&self, rhs: &Self) -> Uint<{nlimbs!($bits) * 2}> {
                    let mut limbs = [Limb::ZERO; nlimbs!($bits) * 2];
                    let mut i = 0;
                    let mut j = 0;

                    while j < nlimbs!($bits) {
                        limbs[i] = rhs.limbs[j];
                        i += 1;
                        j += 1;
                    }

                    j = 0;
                    while j < nlimbs!($bits) {
                        limbs[i] = self.limbs[j];
                        i += 1;
                        j += 1;
                    }

                    Uint { limbs }
                }
            }

            impl Concat for $name {
                type Output = Uint<{nlimbs!($bits) * 2}>;

                fn concat(&self, rhs: &Self) -> Self::Output {
                    self.concat(rhs)
                }
            }

            impl From<($name, $name)> for Uint<{nlimbs!($bits) * 2}> {
                fn from(nums: ($name, $name)) -> Uint<{nlimbs!($bits) * 2}> {
                    nums.1.concat(&nums.0)
                }
            }
        )+
     };
}

#[cfg(feature = "cross-size")]
macro_rules! impl_concat_cross_sizes {
    (($first_type:ident, $first_bits:expr), ($(($second_type:ident, $second_bits:expr)),+ $(,)?)) => {
        $(
            impl ConcatOther<$second_type> for $first_type {
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
                    <$second_type as ConcatOther<$first_type>>::concat(&nums.1, &nums.0)
                }
            }

            impl ConcatOther<$first_type> for $second_type {
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
                    <$first_type as ConcatOther<$second_type>>::concat(&nums.1, &nums.0)
                }
            }
        )+
    };
}

#[cfg(test)]
mod tests {
    #[cfg(feature = "cross-size")]
    use crate::{ConcatOther, U192};
    use crate::{U128, U64};

    #[test]
    fn concat() {
        let hi = U64::from_u64(0x0011223344556677);
        let lo = U64::from_u64(0x8899aabbccddeeff);
        assert_eq!(
            hi.concat(&lo),
            U128::from_be_hex("00112233445566778899aabbccddeeff")
        );
    }

    #[cfg(feature = "cross-size")]
    #[test]
    fn concat_other() {
        let hi = U64::from_u64(0x0011223344556677);
        let lo = U128::from_be_hex("00112233445566778899aabbccddeeff");

        assert_eq!(
            <U64 as ConcatOther<U128>>::concat(&hi, &lo),
            U192::from_be_hex("001122334455667700112233445566778899aabbccddeeff")
        );

        let hi = U128::from_be_hex("00112233445566778899aabbccddeeff");
        let lo = U64::from_u64(0x0011223344556677);

        assert_eq!(
            <U128 as ConcatOther<U64>>::concat(&hi, &lo),
            U192::from_be_hex("00112233445566778899aabbccddeeff0011223344556677")
        );
    }

    #[test]
    fn convert() {
        let res: U128 = U64::ONE.mul_wide(&U64::ONE).into();
        assert_eq!(res, U128::ONE);

        let res: U128 = U64::ONE.square_wide().into();
        assert_eq!(res, U128::ONE);
    }

    #[cfg(feature = "cross-size")]
    #[test]
    fn convert_cross_sizes() {
        let res: U192 = U64::ONE.mul_wide(&U128::ONE).into();
        assert_eq!(res, U192::ONE);
    }
}
