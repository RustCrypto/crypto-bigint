//! Multiplicative inverses of integers in Montgomery form with a modulus set at runtime.

use super::{MontyForm, MontyParams};
use crate::{
    modular::BernsteinYangInverter, traits::Invert, ConstCtOption, Inverter, Odd,
    PrecomputeInverter, PrecomputeInverterWithAdjuster, Uint,
};
use core::fmt;
use subtle::CtOption;

impl<const SAT_LIMBS: usize, const UNSAT_LIMBS: usize> MontyForm<SAT_LIMBS>
where
    Odd<Uint<SAT_LIMBS>>: PrecomputeInverter<
        Inverter = BernsteinYangInverter<SAT_LIMBS, UNSAT_LIMBS>,
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
        Inverter = BernsteinYangInverter<SAT_LIMBS, UNSAT_LIMBS>,
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
        Inverter = BernsteinYangInverter<SAT_LIMBS, UNSAT_LIMBS>,
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
    use crate::{Invert, Inverter, Odd, PrecomputeInverter, U256};

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
        let x_mod = MontyForm::new(&x, params);

        let inv = x_mod.invert().unwrap();
        let res = x_mod * inv;

        assert_eq!(res.retrieve(), U256::ONE);
    }

    #[test]
    fn test_self_inverse_precomuted() {
        let params = params();
        let x =
            U256::from_be_hex("77117F1273373C26C700D076B3F780074D03339F56DD0EFB60E7F58441FD3685");
        let x_mod = MontyForm::new(&x, params);

        let inverter = params.precompute_inverter();
        let inv = inverter.invert(&x_mod).unwrap();
        let res = x_mod * inv;

        assert_eq!(res.retrieve(), U256::ONE);
    }

    //  Test to illustrate a potential problem with the Bernstein&Yang code to
    //  invert numbers in Montgomery form. The specific parameters shown here
    //  come from intermittent test failures of [homomorphic_mul] in the
    //  Synedrion signining library (i.e. parameters are generated with an
    //  unseeded CSPRNG).
    //  Run the test with `cargo t v06_inversion`.
    //  After this test follows a test doing the same thing, but using v0.5.5
    //
    //  [homomorphic_mul]: https://github.com/dvdplm/synedrion/blob/520e3246e6032a100db64eef47b3dee62cd7c055/synedrion/src/paillier/encryption.rs#L518
    #[test]
    fn v06_inversion() {
        use crate::U2048;

        let modulus = Odd::new(U2048::from_be_hex("5DC56576A9F077F2FD05CC35DD0B1060857CD5A44011891ED05D8C56359A9302FC9FB1D6B2FF411FAC318009C519FB7D883ACF327C2FC1181642B7A076C7DB244AB265D20605AA55EB04B5F5100B961A684033BD4E98A45DFD2AAD4B13625808FF3C947BC3712CE8D2A5688579F08B5B523B9C6EC3361535379620F49E94C85508A6E0D264A284E3F6B3C54447D5DB9A421D1FBE2A1F59FFF92D1D9F68985E51C316CA027B4E6D9AAEED0D9F41DF77CFF021BF8F7A2E55E1F2B80859C466686305671C615757BA9712513A92764F399B486723549976024BEFF7A9484C40F5E765904E3477E1B6849468D513C26997D2A9BD038511C98E48FAE3493EC6A7FE49")).unwrap();
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

    // Version of the above test using v0.5.5
    #[test]
    fn v05_inversion() {
        use crypto_bigint_05::{
            modular::runtime_mod::{DynResidue, DynResidueParams},
            U2048,
        };
        let modulus = U2048::from_be_hex("5DC56576A9F077F2FD05CC35DD0B1060857CD5A44011891ED05D8C56359A9302FC9FB1D6B2FF411FAC318009C519FB7D883ACF327C2FC1181642B7A076C7DB244AB265D20605AA55EB04B5F5100B961A684033BD4E98A45DFD2AAD4B13625808FF3C947BC3712CE8D2A5688579F08B5B523B9C6EC3361535379620F49E94C85508A6E0D264A284E3F6B3C54447D5DB9A421D1FBE2A1F59FFF92D1D9F68985E51C316CA027B4E6D9AAEED0D9F41DF77CFF021BF8F7A2E55E1F2B80859C466686305671C615757BA9712513A92764F399B486723549976024BEFF7A9484C40F5E765904E3477E1B6849468D513C26997D2A9BD038511C98E48FAE3493EC6A7FE49");
        let params = DynResidueParams::new(&modulus);
        let int = U2048::from_be_hex("408A71A0709CE2CD00E6F48D4D93E1AF2D2A788810B2F3948CC2DEC041BECA2801CDF12A70B044881BE452BA9BEB246D2E4899D7CFE351CE61F95D8DE656146DF610CE4428BFB4CE8B60D3EF8B038C031F59460BDA91F30550C826C912997B2E8849295AFDC104635A9401A5A0E0A8B052D0A3CB50E6E7671D9D68ADB4210A5502341DF41349924B1792DDDE6FA393E4462A5A8D8EE4D4096FBDB66EE4025D8B9167023A02D2661FEE84DB942F02EDF5DFE214E84AA5F4A308E11DEE9503EB0C550111C53A6580B31655F20B75C822BB44F01A2FB1C9A727790AA3BBD6AF32BCDC44365B9774CE909264A5BF2BDF79C0F1169226A1FDA309222B4017023BF6D2");
        let mont = DynResidue::new(&int, params);

        let (inverted, choice) = mont.invert();

        let expected_inv = {
            let int = U2048::from_be_hex("579F198AFBD0EC0921E8626D386C7F8080F8C0668284BE38FE5B9E67AA81A6F637FFEDBB76E9CF68E5E7BA9892D4938DB90906686CEF06A94D16AA9CDA0C0E24DAB9AB72303316266BF4DCF449E00D8F7795819C06CA5921A31B40A2AB1B0D7C264144D0372D59ADD5754FE02B1328E159B4B58767FFB623D1A6B3CC89B3F724A647A9AFCB55ACD02491544849A4603C013C5313DEC80A8AC46C268BA1245BA1B9D05386A560E1CBACE4F7C39873471101C19C6CE07D4CDDE06B1557081F5C838452135A16216285E1AC92A1F30263AC148BBE74A9397514D6B17E7473C703D965EA68054D4AA5AC9967729997A898AFA78C8D418871B30F502F3E01B89F1C3E");
            DynResidue::new(&int, params)
        };

        assert!(bool::from(choice));
        assert_eq!(inverted, expected_inv);

        let one = mont * inverted;
        assert_eq!(one.retrieve(), U2048::ONE);
    }

    /// This test use the same inputs as the `inversion_v06_vs_v055` test above
    /// but using the `num-modular` code. That crate lacks support for big integer Montgomery form
    /// so for this test the values are in normal form.
    ///
    /// This test passes and agrees with crypto-bigint v0.5.5.
    #[test]
    fn invert_with_num_modular() {
        let modulus = BigUint::from_be_bytes(&hex!(
            "5DC56576A9F077F2FD05CC35DD0B1060857CD5A44011891ED05D8C56359A9302FC9FB1D6B2FF411FAC318009C519FB7D883ACF327C2FC1181642B7A076C7DB244AB265D20605AA55EB04B5F5100B961A684033BD4E98A45DFD2AAD4B13625808FF3C947BC3712CE8D2A5688579F08B5B523B9C6EC3361535379620F49E94C85508A6E0D264A284E3F6B3C54447D5DB9A421D1FBE2A1F59FFF92D1D9F68985E51C316CA027B4E6D9AAEED0D9F41DF77CFF021BF8F7A2E55E1F2B80859C466686305671C615757BA9712513A92764F399B486723549976024BEFF7A9484C40F5E765904E3477E1B6849468D513C26997D2A9BD038511C98E48FAE3493EC6A7FE49"
        ));

        let int = BigUint::from_be_bytes(&hex!("408A71A0709CE2CD00E6F48D4D93E1AF2D2A788810B2F3948CC2DEC041BECA2801CDF12A70B044881BE452BA9BEB246D2E4899D7CFE351CE61F95D8DE656146DF610CE4428BFB4CE8B60D3EF8B038C031F59460BDA91F30550C826C912997B2E8849295AFDC104635A9401A5A0E0A8B052D0A3CB50E6E7671D9D68ADB4210A5502341DF41349924B1792DDDE6FA393E4462A5A8D8EE4D4096FBDB66EE4025D8B9167023A02D2661FEE84DB942F02EDF5DFE214E84AA5F4A308E11DEE9503EB0C550111C53A6580B31655F20B75C822BB44F01A2FB1C9A727790AA3BBD6AF32BCDC44365B9774CE909264A5BF2BDF79C0F1169226A1FDA309222B4017023BF6D2"));
        let inverted = int.clone().invm(&modulus).expect("inverse exists");

        let expected_inv = BigUint::from_bytes_be(&hex!("579F198AFBD0EC0921E8626D386C7F8080F8C0668284BE38FE5B9E67AA81A6F637FFEDBB76E9CF68E5E7BA9892D4938DB90906686CEF06A94D16AA9CDA0C0E24DAB9AB72303316266BF4DCF449E00D8F7795819C06CA5921A31B40A2AB1B0D7C264144D0372D59ADD5754FE02B1328E159B4B58767FFB623D1A6B3CC89B3F724A647A9AFCB55ACD02491544849A4603C013C5313DEC80A8AC46C268BA1245BA1B9D05386A560E1CBACE4F7C39873471101C19C6CE07D4CDDE06B1557081F5C838452135A16216285E1AC92A1F30263AC148BBE74A9397514D6B17E7473C703D965EA68054D4AA5AC9967729997A898AFA78C8D418871B30F502F3E01B89F1C3E"));
        assert_eq!(inverted, expected_inv);
        let one = int.mulm(inverted, &modulus);
        assert_eq!(one, BigUint::one());
    }

    // v0.6 test that creates random U1024s, inverts and sanity checks the result.
    #[test]
    fn v06_invert_random_uint() {
        use crate::{Integer, NonZero, RandomMod, U1024, U2048};
        use rand_chacha::ChaChaRng;
        use rand_core::{CryptoRngCore, SeedableRng};

        fn random_invertible(
            monty_params: MontyParams<16>,
            rng: &mut impl CryptoRngCore,
        ) -> (U1024, MontyForm<16>, MontyForm<16>) {
            let modulus = monty_params.modulus().to_nz().unwrap();
            loop {
                let r = U1024::random_mod(rng, &modulus);
                let rm = <U1024 as Integer>::Monty::new(&r, monty_params);
                let rm_inv = rm.invert();
                if rm_inv.is_some().into() {
                    return (r, rm, rm_inv.unwrap());
                }
            }
        }

        let mut rng = ChaChaRng::from_seed([17u8; 32]);
        let modulus = U1024::from([
            0xd69d42ede255db9d,
            0x20d23f0e7e55c2f3,
            0xb11955f4354ad01e,
            0xe1598344a83da132,
            0xa40162a5315c9b7f,
            0xa3e41cc5720f4dca,
            0x3a28db743e07f87b,
            0x717d2332171a2bd7,
            0x7f6917818473334e,
            0x7fc6c2ffd071667d,
            0x1bdb77d72f57ac49,
            0x3c857fff2fe7f7ee,
            0x33ca8e3a359428ad,
            0x12a442daca8af09d,
            0x872ac90b36ebd1bc,
            0x9aefced07fa13351,
        ]);

        let monty_params = MontyParams::new_vartime(modulus.to_odd().unwrap());
        for _ in 0..100 {
            let (r, rm, rmi) = random_invertible(monty_params, &mut rng);
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

    // v0.5.5 test that creates random U1024s, inverts and sanity checks the result.
    #[test]
    fn v05_invert_random_uint() {
        use crypto_bigint_05::{
            modular::runtime_mod::{DynResidue, DynResidueParams},
            NonZero, RandomMod, U1024, U2048,
        };
        use rand_chacha::ChaChaRng;
        use rand_core::{CryptoRngCore, SeedableRng};

        fn random_invertible(
            monty_params: DynResidueParams<16>,
            rng: &mut impl CryptoRngCore,
        ) -> (U1024, DynResidue<16>, DynResidue<16>) {
            let modulus = monty_params.modulus().clone();
            loop {
                let r = U1024::random_mod(rng, &NonZero::new(modulus).unwrap());
                let rm = DynResidue::new(&r, monty_params);
                let (rm_inv, rm_inv_opt) = rm.invert();
                if bool::from(rm_inv_opt) {
                    return (r, rm, rm_inv);
                }
            }
        }
        let mut rng = ChaChaRng::from_seed([17u8; 32]);
        let modulus = U1024::from([
            0xd69d42ede255db9d,
            0x20d23f0e7e55c2f3,
            0xb11955f4354ad01e,
            0xe1598344a83da132,
            0xa40162a5315c9b7f,
            0xa3e41cc5720f4dca,
            0x3a28db743e07f87b,
            0x717d2332171a2bd7,
            0x7f6917818473334e,
            0x7fc6c2ffd071667d,
            0x1bdb77d72f57ac49,
            0x3c857fff2fe7f7ee,
            0x33ca8e3a359428ad,
            0x12a442daca8af09d,
            0x872ac90b36ebd1bc,
            0x9aefced07fa13351,
        ]);

        let monty_params = DynResidueParams::new(&modulus);
        for _ in 0..100 {
            let (r, rm, rmi) = random_invertible(monty_params, &mut rng);

            let one_monty = rm * rmi;
            assert_eq!(one_monty, DynResidue::one(monty_params));
            assert_eq!(one_monty.retrieve(), U1024::ONE);

            let one = rmi.retrieve() * r;
            let wide_modulus = NonZero::new(Into::<U2048>::into(&modulus)).unwrap();
            assert_eq!(one % wide_modulus, U2048::ONE);

            let (ri, _) = r.inv_mod(&modulus);
            assert_eq!(ri, rmi.retrieve());
        }
    }
}
