//! Multiplicative inverses of integers in Montgomery form with a modulus set at runtime.

use super::{MontyForm, MontyParams};
use crate::{
    modular::SafeGcdInverter, traits::Invert, ConstCtOption, Inverter, Odd, PrecomputeInverter,
    PrecomputeInverterWithAdjuster, Uint,
};
use core::fmt;
use subtle::CtOption;

impl<const SAT_LIMBS: usize, const UNSAT_LIMBS: usize> MontyForm<SAT_LIMBS>
where
    Odd<Uint<SAT_LIMBS>>: PrecomputeInverter<
        Inverter = SafeGcdInverter<SAT_LIMBS, UNSAT_LIMBS>,
        Output = Uint<SAT_LIMBS>,
    >,
{
    /// Computes `self^-1` representing the multiplicative inverse of `self`.
    /// I.e. `self * self^-1 = 1`.
    /// If the number was invertible, the second element of the tuple is the truthy value,
    /// otherwise it is the falsy value (in which case the first element's value is unspecified).
    pub const fn inv(&self) -> ConstCtOption<Self> {
        let inverter = <Odd<Uint<SAT_LIMBS>> as PrecomputeInverter>::Inverter::new(
            &self.params.modulus,
            &self.params.r2,
        );

        let maybe_inverse = inverter.inv(&self.montgomery_form);
        let (inverse, inverse_is_some) = maybe_inverse.components_ref();

        let ret = Self {
            montgomery_form: *inverse,
            params: self.params,
        };

        ConstCtOption::new(ret, inverse_is_some)
    }
}

impl<const SAT_LIMBS: usize, const UNSAT_LIMBS: usize> Invert for MontyForm<SAT_LIMBS>
where
    Odd<Uint<SAT_LIMBS>>: PrecomputeInverter<
        Inverter = SafeGcdInverter<SAT_LIMBS, UNSAT_LIMBS>,
        Output = Uint<SAT_LIMBS>,
    >,
{
    type Output = CtOption<Self>;

    fn invert(&self) -> Self::Output {
        self.inv().into()
    }
}

impl<const LIMBS: usize> PrecomputeInverter for MontyParams<LIMBS>
where
    Odd<Uint<LIMBS>>:
        PrecomputeInverter<Output = Uint<LIMBS>> + PrecomputeInverterWithAdjuster<Uint<LIMBS>>,
{
    type Inverter = MontyFormInverter<LIMBS>;
    type Output = MontyForm<LIMBS>;

    fn precompute_inverter(&self) -> MontyFormInverter<LIMBS> {
        MontyFormInverter {
            inverter: self.modulus.precompute_inverter_with_adjuster(&self.r2),
            params: *self,
        }
    }
}

/// Bernstein-Yang inverter which inverts [`MontyForm`] types.
pub struct MontyFormInverter<const LIMBS: usize>
where
    Odd<Uint<LIMBS>>: PrecomputeInverter<Output = Uint<LIMBS>>,
{
    inverter: <Odd<Uint<LIMBS>> as PrecomputeInverter>::Inverter,
    params: MontyParams<LIMBS>,
}

impl<const LIMBS: usize> Inverter for MontyFormInverter<LIMBS>
where
    Odd<Uint<LIMBS>>: PrecomputeInverter<Output = Uint<LIMBS>>,
{
    type Output = MontyForm<LIMBS>;

    fn invert(&self, value: &MontyForm<LIMBS>) -> CtOption<Self::Output> {
        debug_assert_eq!(self.params, value.params);

        self.inverter
            .invert(&value.montgomery_form)
            .map(|montgomery_form| MontyForm {
                montgomery_form,
                params: value.params,
            })
    }
}

impl<const SAT_LIMBS: usize, const UNSAT_LIMBS: usize> fmt::Debug for MontyFormInverter<SAT_LIMBS>
where
    Odd<Uint<SAT_LIMBS>>: PrecomputeInverter<
        Inverter = SafeGcdInverter<SAT_LIMBS, UNSAT_LIMBS>,
        Output = Uint<SAT_LIMBS>,
    >,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("MontyFormInverter")
            .field("modulus", &self.inverter.modulus)
            .finish()
    }
}

#[cfg(test)]
mod tests {
    use hex_literal::hex;
    use num_bigint::BigUint;
    use num_modular::{ModularCoreOps, ModularUnaryOps};
    use num_traits::{FromBytes, One};

    use super::{MontyForm, MontyParams};
    use crate::{Invert, Inverter, Odd, PrecomputeInverter, U2048, U256};

    // Random modulus.
    const MODULUS: [u8; 256] = hex!("5DC56576A9F077F2FD05CC35DD0B1060857CD5A44011891ED05D8C56359A9302FC9FB1D6B2FF411FAC318009C519FB7D883ACF327C2FC1181642B7A076C7DB244AB265D20605AA55EB04B5F5100B961A684033BD4E98A45DFD2AAD4B13625808FF3C947BC3712CE8D2A5688579F08B5B523B9C6EC3361535379620F49E94C85508A6E0D264A284E3F6B3C54447D5DB9A421D1FBE2A1F59FFF92D1D9F68985E51C316CA027B4E6D9AAEED0D9F41DF77CFF021BF8F7A2E55E1F2B80859C466686305671C615757BA9712513A92764F399B486723549976024BEFF7A9484C40F5E765904E3477E1B6849468D513C26997D2A9BD038511C98E48FAE3493EC6A7FE49");

    #[cfg(feature = "rand_core")]
    mod randomized_tests {
        use super::*;
        use crate::{Integer, NonZero, Uint, U1024, U4096, U8192};

        use crate::RandomMod;
        use rand_chacha::ChaChaRng;
        use rand_core::{CryptoRngCore, SeedableRng};

        // Seed used to ensure deterministc random sequences in tests.
        const RANDOM_SEED: [u8; 32] = [17; 32];

        #[cfg(target_pointer_width = "32")]
        const LIMBS_1024: usize = 32;
        #[cfg(target_pointer_width = "32")]
        const LIMBS_2048: usize = 64;
        #[cfg(target_pointer_width = "32")]
        const LIMBS_4096: usize = 128;

        #[cfg(target_pointer_width = "64")]
        pub const LIMBS_1024: usize = 16;
        #[cfg(target_pointer_width = "64")]
        pub const LIMBS_2048: usize = 32;
        #[cfg(target_pointer_width = "64")]
        pub const LIMBS_4096: usize = 64;
        // Generates a random `U1024` and returns it as a tuple in: normal form, montgomery form,
        // inverted montgomery form and the normal form inverse from the num_modular crate.
        fn random_invertible_u1024(
            monty_params: MontyParams<LIMBS_1024>,
            rng: &mut impl CryptoRngCore,
        ) -> (U1024, MontyForm<LIMBS_1024>, MontyForm<LIMBS_1024>, BigUint) {
            let modulus = monty_params.modulus().to_nz().unwrap();
            loop {
                let r = Uint::random_mod(rng, &modulus);
                let rm = <U1024 as Integer>::Monty::new(&r, monty_params);
                let rm_inv = rm.invert();
                if rm_inv.is_some().into() {
                    // Calculate the inverse using the num_modular crate as well
                    let num_modular_modulus =
                        BigUint::from_be_bytes(&monty_params.modulus().0.to_be_bytes());
                    let num_modular_inverse = BigUint::from_be_bytes(&r.to_be_bytes())
                        .clone()
                        .invm(&num_modular_modulus)
                        .unwrap();

                    return (r, rm, rm_inv.unwrap(), num_modular_inverse);
                }
            }
        }
        // Generates a random `U2048` and returns it as a tuple in: normal form, montgomery form,
        // inverted montgomery form and the normal form inverse from the num_modular crate.
        fn random_invertible_u2048(
            monty_params: MontyParams<LIMBS_2048>,
            rng: &mut impl CryptoRngCore,
        ) -> (U2048, MontyForm<LIMBS_2048>, MontyForm<LIMBS_2048>, BigUint) {
            let modulus = monty_params.modulus().to_nz().unwrap();
            loop {
                let r = Uint::random_mod(rng, &modulus);
                let rm = <U2048 as Integer>::Monty::new(&r, monty_params);
                let rm_inv = rm.invert();
                if rm_inv.is_some().into() {
                    // Calculate the inverse using the num_modular crate as well
                    let num_modular_modulus =
                        BigUint::from_be_bytes(&monty_params.modulus().0.to_be_bytes());
                    let num_modular_inverse = BigUint::from_be_bytes(&r.to_be_bytes())
                        .clone()
                        .invm(&num_modular_modulus)
                        .unwrap();

                    return (r, rm, rm_inv.unwrap(), num_modular_inverse);
                }
            }
        }

        // Generates a random `U4096` and returns it as a tuple in: normal form, montgomery form,
        // inverted montgomery form and the normal form inverse from the num_modular crate.
        fn random_invertible_u4096(
            monty_params: MontyParams<LIMBS_4096>,
            rng: &mut impl CryptoRngCore,
        ) -> (U4096, MontyForm<LIMBS_4096>, MontyForm<LIMBS_4096>, BigUint) {
            let modulus = monty_params.modulus().to_nz().unwrap();
            loop {
                let r = Uint::random_mod(rng, &modulus);
                let rm = <U4096 as Integer>::Monty::new(&r, monty_params);
                let rm_inv = rm.invert();
                if rm_inv.is_some().into() {
                    // Calculate the inverse using the num_modular crate as well
                    let num_modular_modulus =
                        BigUint::from_be_bytes(&monty_params.modulus().0.to_be_bytes());
                    let num_modular_inverse = BigUint::from_be_bytes(&r.to_be_bytes())
                        .clone()
                        .invm(&num_modular_modulus)
                        .unwrap();

                    return (r, rm, rm_inv.unwrap(), num_modular_inverse);
                }
            }
        }

        // Creates random U1024s, inverts and sanity checks the result.
        #[test]
        fn inversion_random_uints_u1024() {
            let mut rng = ChaChaRng::from_seed(RANDOM_SEED);
            let modulus = U1024::from_be_hex(concat!(
                "1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",
                "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",
                "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",
                "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",
            ));
            let wide_modulus = NonZero::new(Into::<U2048>::into(&modulus)).unwrap();
            let monty_params = MontyParams::new_vartime(modulus.to_odd().unwrap());

            // Tested up to 10_000_000
            for _ in 0..100 {
                let (rand_uint, rand_uint_monty, rand_uint_monty_inv, num_modular_inv) =
                    random_invertible_u1024(monty_params, &mut rng);
                let one_monty = rand_uint_monty * rand_uint_monty_inv;

                // Inversion works in monty form
                assert_eq!(
                    one_monty,
                    MontyForm::one(monty_params),
                    "a*a⁻¹ ≠ 1 (monty form)\nmodulus: {:01024b}",
                    modulus
                );
                // …and in normal form
                assert_eq!(one_monty.retrieve(), U1024::ONE, "a*a⁻¹ ≠ 1 (normal form)");

                // …and when converted back to normal form and used in a widening operation
                let one = rand_uint_monty_inv.retrieve().widening_mul(&rand_uint);
                assert_eq!(
                    one % wide_modulus,
                    U2048::ONE,
                    "a*a⁻¹ ≠ 1 (normal form, wide)"
                );

                // …and agrees with normal form inversion
                let normal_form_inv = rand_uint.inv_mod(&modulus).unwrap();
                assert_eq!(
                    normal_form_inv,
                    rand_uint_monty_inv.retrieve(),
                    "a*a⁻¹ ≠ 1 (normal form inverted)"
                );

                // …and agrees with the num_modular crate
                assert_eq!(
                    BigUint::from_be_bytes(&normal_form_inv.to_be_bytes()),
                    num_modular_inv,
                    "num_modular ≠ crypto_bigint"
                )
            }
        }

        #[test]
        fn inversion_random_uints_u2048() {
            let mut rng = ChaChaRng::from_seed(RANDOM_SEED);
            let modulus = U2048::from_be_hex(concat!(
                "1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",
                "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",
                "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",
                "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",
                "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",
                "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",
                "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",
                "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"
            ));
            let wide_modulus = NonZero::new(Into::<U4096>::into(&modulus)).unwrap();
            let monty_params = MontyParams::new_vartime(modulus.to_odd().unwrap());
            for _ in 0..100 {
                let (rand_uint, rand_uint_monty, rand_uint_monty_inv, num_modular_inv) =
                    random_invertible_u2048(monty_params, &mut rng);
                let one_monty = rand_uint_monty * rand_uint_monty_inv;

                // Inversion works in monty form
                assert_eq!(
                    one_monty,
                    MontyForm::one(monty_params),
                    "a*a⁻¹ ≠ 1 (monty form)\nmodulus: {:02048b}",
                    modulus
                );
                // …and in normal form
                assert_eq!(one_monty.retrieve(), U2048::ONE, "a*a⁻¹ ≠ 1 (normal form)");

                // …and when converted back to normal form and used in a widening operation
                let one = rand_uint_monty_inv.retrieve().widening_mul(&rand_uint);
                assert_eq!(
                    one % wide_modulus,
                    U4096::ONE,
                    "a*a⁻¹ ≠ 1 (normal form, wide)"
                );

                // …and agrees with normal form inversion
                let normal_form_inv = rand_uint.inv_mod(&modulus).unwrap();
                assert_eq!(
                    normal_form_inv,
                    rand_uint_monty_inv.retrieve(),
                    "a*a⁻¹ ≠ 1 (normal form inverted)"
                );

                // …and agrees with the num_modular crate
                assert_eq!(
                    BigUint::from_be_bytes(&normal_form_inv.to_be_bytes()),
                    num_modular_inv,
                    "num_modular ≠ crypto_bigint"
                )
            }
        }

        #[test]
        fn inversion_random_uints_u4096() {
            let mut rng = ChaChaRng::from_seed(RANDOM_SEED);
            let modulus = U4096::from_be_hex(concat!(
                "07ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",
                "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",
                "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",
                "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",
                "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",
                "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",
                "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",
                "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",
                "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",
                "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",
                "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",
                "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",
                "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",
                "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",
                "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",
                "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",
            ));
            let wide_modulus = NonZero::new(Into::<U8192>::into(&modulus)).unwrap();
            let monty_params = MontyParams::new_vartime(modulus.to_odd().unwrap());

            for _ in 0..20 {
                let (rand_uint, rand_uint_monty, rand_uint_monty_inv, num_modular_inv) =
                    random_invertible_u4096(monty_params, &mut rng);
                let one_monty = rand_uint_monty * rand_uint_monty_inv;

                // Inversion works in monty form
                assert_eq!(
                    one_monty,
                    MontyForm::one(monty_params),
                    "a*a⁻¹ ≠ 1 (monty form)\nmodulus: {:02048b}",
                    modulus
                );
                // …and in normal form
                assert_eq!(one_monty.retrieve(), U4096::ONE, "a*a⁻¹ ≠ 1 (normal form)");

                // …and when converted back to normal form and used in a widening operation
                let one = rand_uint_monty_inv.retrieve().widening_mul(&rand_uint);
                assert_eq!(
                    one % wide_modulus,
                    U8192::ONE,
                    "a*a⁻¹ ≠ 1 (normal form, wide)"
                );

                // …and agrees with normal form inversion
                let normal_form_inv = rand_uint.inv_mod(&modulus).unwrap();
                assert_eq!(
                    normal_form_inv,
                    rand_uint_monty_inv.retrieve(),
                    "a*a⁻¹ ≠ 1 (normal form inverted)"
                );

                // …and agrees with the num_modular crate
                assert_eq!(
                    BigUint::from_be_bytes(&normal_form_inv.to_be_bytes()),
                    num_modular_inv,
                    "num_modular ≠ crypto_bigint"
                )
            }
        }

        // Creates random U1024s, inverts and sanity checks the result.
        #[test]
        fn invert_random_u1024s() {
            let mut rng = ChaChaRng::from_seed(RANDOM_SEED);
            let modulus = U1024::from_be_hex("d69d42ede255db9d20d23f0e7e55c2f3b11955f4354ad01ee1598344a83da132a40162a5315c9b7fa3e41cc5720f4dca3a28db743e07f87b717d2332171a2bd77f6917818473334e7fc6c2ffd071667d1bdb77d72f57ac493c857fff2fe7f7ee33ca8e3a359428ad12a442daca8af09d872ac90b36ebd1bc9aefced07fa13351");
            let monty_params = MontyParams::new_vartime(modulus.to_odd().unwrap());
            for _ in 0..100 {
                let (r, rm, rmi, _) = random_invertible_u1024(monty_params, &mut rng);
                let one_monty = rm * rmi;
                assert_eq!(one_monty, MontyForm::one(monty_params));
                assert_eq!(one_monty.retrieve(), U1024::ONE);

                let one = rmi.retrieve().widening_mul(&r);
                let wide_modulus = NonZero::new(Into::<U2048>::into(&modulus)).unwrap();
                assert_eq!(one % wide_modulus, U2048::ONE);

                let ri = r.inv_mod(&modulus).unwrap();
                assert_eq!(ri, rmi.retrieve());
            }
        }
    }

    fn params() -> MontyParams<{ U256::LIMBS }> {
        MontyParams::new_vartime(Odd::<U256>::from_be_hex(
            "15477BCCEFE197328255BFA79A1217899016D927EF460F4FF404029D24FA4409",
        ))
    }

    #[test]
    fn test_self_inverse() {
        let params = params();
        let x =
            U256::from_be_hex("77117F1273373C26C700D076B3F780074D03339F56DD0EFB60E7F58441FD3685");
        let x_monty = MontyForm::new(&x, params);

        let inv = x_monty.invert().unwrap();
        let res = x_monty * inv;

        assert_eq!(res.retrieve(), U256::ONE);
    }

    #[test]
    fn test_self_inverse_precomuted() {
        let params = params();
        let x =
            U256::from_be_hex("77117F1273373C26C700D076B3F780074D03339F56DD0EFB60E7F58441FD3685");
        let x_monty = MontyForm::new(&x, params);

        let inverter = params.precompute_inverter();
        let inv = inverter.invert(&x_monty).unwrap();
        let res = x_monty * inv;

        assert_eq!(res.retrieve(), U256::ONE);
    }

    #[test]
    fn invert_u2048() {
        let modulus = Odd::new(U2048::from_be_slice(&MODULUS)).unwrap();
        let params = MontyParams::new_vartime(modulus);
        let int = U2048::from_be_hex("408A71A0709CE2CD00E6F48D4D93E1AF2D2A788810B2F3948CC2DEC041BECA2801CDF12A70B044881BE452BA9BEB246D2E4899D7CFE351CE61F95D8DE656146DF610CE4428BFB4CE8B60D3EF8B038C031F59460BDA91F30550C826C912997B2E8849295AFDC104635A9401A5A0E0A8B052D0A3CB50E6E7671D9D68ADB4210A5502341DF41349924B1792DDDE6FA393E4462A5A8D8EE4D4096FBDB66EE4025D8B9167023A02D2661FEE84DB942F02EDF5DFE214E84AA5F4A308E11DEE9503EB0C550111C53A6580B31655F20B75C822BB44F01A2FB1C9A727790AA3BBD6AF32BCDC44365B9774CE909264A5BF2BDF79C0F1169226A1FDA309222B4017023BF6D2");
        let mont = MontyForm::new(&int, params);
        let inverted = mont.invert();

        // This is what v0.5.5 outputs using the same inputs.
        let expected_inv = {
            let int = U2048::from_be_hex("579F198AFBD0EC0921E8626D386C7F8080F8C0668284BE38FE5B9E67AA81A6F637FFEDBB76E9CF68E5E7BA9892D4938DB90906686CEF06A94D16AA9CDA0C0E24DAB9AB72303316266BF4DCF449E00D8F7795819C06CA5921A31B40A2AB1B0D7C264144D0372D59ADD5754FE02B1328E159B4B58767FFB623D1A6B3CC89B3F724A647A9AFCB55ACD02491544849A4603C013C5313DEC80A8AC46C268BA1245BA1B9D05386A560E1CBACE4F7C39873471101C19C6CE07D4CDDE06B1557081F5C838452135A16216285E1AC92A1F30263AC148BBE74A9397514D6B17E7473C703D965EA68054D4AA5AC9967729997A898AFA78C8D418871B30F502F3E01B89F1C3E");
            MontyForm::new(&int, params)
        };
        assert!(bool::from(inverted.is_some()));
        let inverted = inverted.unwrap();
        assert_eq!(inverted, expected_inv);

        let one = mont * inverted;
        assert_eq!(one.retrieve(), U2048::ONE);
    }

    /// This test use the same inputs as the test above
    /// but using the `num-modular` crate. That crate lacks support for big integer Montgomery form
    /// so for this test the values are in normal form.
    #[test]
    fn invert_u2048_with_num_modular() {
        let modulus = BigUint::from_be_bytes(&MODULUS);

        let int = BigUint::from_be_bytes(&hex!("408A71A0709CE2CD00E6F48D4D93E1AF2D2A788810B2F3948CC2DEC041BECA2801CDF12A70B044881BE452BA9BEB246D2E4899D7CFE351CE61F95D8DE656146DF610CE4428BFB4CE8B60D3EF8B038C031F59460BDA91F30550C826C912997B2E8849295AFDC104635A9401A5A0E0A8B052D0A3CB50E6E7671D9D68ADB4210A5502341DF41349924B1792DDDE6FA393E4462A5A8D8EE4D4096FBDB66EE4025D8B9167023A02D2661FEE84DB942F02EDF5DFE214E84AA5F4A308E11DEE9503EB0C550111C53A6580B31655F20B75C822BB44F01A2FB1C9A727790AA3BBD6AF32BCDC44365B9774CE909264A5BF2BDF79C0F1169226A1FDA309222B4017023BF6D2"));
        let inverted = int.clone().invm(&modulus).expect("inverse exists");

        let expected_inv = BigUint::from_bytes_be(&hex!("579F198AFBD0EC0921E8626D386C7F8080F8C0668284BE38FE5B9E67AA81A6F637FFEDBB76E9CF68E5E7BA9892D4938DB90906686CEF06A94D16AA9CDA0C0E24DAB9AB72303316266BF4DCF449E00D8F7795819C06CA5921A31B40A2AB1B0D7C264144D0372D59ADD5754FE02B1328E159B4B58767FFB623D1A6B3CC89B3F724A647A9AFCB55ACD02491544849A4603C013C5313DEC80A8AC46C268BA1245BA1B9D05386A560E1CBACE4F7C39873471101C19C6CE07D4CDDE06B1557081F5C838452135A16216285E1AC92A1F30263AC148BBE74A9397514D6B17E7473C703D965EA68054D4AA5AC9967729997A898AFA78C8D418871B30F502F3E01B89F1C3E"));
        assert_eq!(inverted, expected_inv);
        let one = int.mulm(inverted, &modulus);
        assert_eq!(one, BigUint::one());
    }
}
