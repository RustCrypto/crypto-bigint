use crate::{modular::pow::pow_montgomery_form, PowBoundedExp, Uint};
#[cfg(feature = "alloc")]
extern crate alloc;
use super::{Residue, ResidueParams};
#[cfg(feature = "alloc")]
use crate::modular::multiexp::multi_exponentiate_montgomery_form;
#[cfg(feature = "alloc")]
use alloc::vec::Vec;

impl<MOD: ResidueParams<LIMBS>, const LIMBS: usize> Residue<MOD, LIMBS> {
    /// Raises to the `exponent` power.
    pub const fn pow<const RHS_LIMBS: usize>(
        &self,
        exponent: &Uint<RHS_LIMBS>,
    ) -> Residue<MOD, LIMBS> {
        self.pow_bounded_exp(exponent, Uint::<RHS_LIMBS>::BITS)
    }

    /// Raises to the `exponent` power,
    /// with `exponent_bits` representing the number of (least significant) bits
    /// to take into account for the exponent.
    ///
    /// NOTE: `exponent_bits` may be leaked in the time pattern.
    pub const fn pow_bounded_exp<const RHS_LIMBS: usize>(
        &self,
        exponent: &Uint<RHS_LIMBS>,
        exponent_bits: usize,
    ) -> Residue<MOD, LIMBS> {
        Self {
            montgomery_form: pow_montgomery_form(
                &self.montgomery_form,
                exponent,
                exponent_bits,
                &MOD::MODULUS,
                &MOD::R,
                MOD::MOD_NEG_INV,
            ),
            phantom: core::marker::PhantomData,
        }
    }

    #[cfg(feature = "alloc")]
    pub fn multi_exponentiate(
        bases_and_exponents: Vec<(Self, Uint<LIMBS>)>,
    ) -> Residue<MOD, LIMBS> {
        Self::multi_exponentiate_bounded_exp(bases_and_exponents, Uint::<LIMBS>::BITS)
    }

    #[cfg(feature = "alloc")]
    pub fn multi_exponentiate_bounded_exp(
        bases_and_exponents: Vec<(Self, Uint<LIMBS>)>,
        exponent_bits: usize,
    ) -> Residue<MOD, LIMBS> {
        let bases_and_exponents: Vec<(Uint<LIMBS>, Uint<LIMBS>)> = bases_and_exponents
            .iter()
            .map(|(base, exp)| (base.montgomery_form, *exp))
            .collect();
        Self {
            montgomery_form: multi_exponentiate_montgomery_form(
                bases_and_exponents,
                exponent_bits,
                &MOD::MODULUS,
                &MOD::R,
                MOD::MOD_NEG_INV,
            ),
            phantom: core::marker::PhantomData,
        }
    }
}

impl<MOD: ResidueParams<LIMBS>, const LIMBS: usize> PowBoundedExp<Uint<LIMBS>>
    for Residue<MOD, LIMBS>
{
    fn pow_bounded_exp(&self, exponent: &Uint<LIMBS>, exponent_bits: usize) -> Self {
        self.pow_bounded_exp(exponent, exponent_bits)
    }
}

#[cfg(test)]
mod tests {
    use crate::{const_residue, impl_modulus, modular::constant_mod::ResidueParams, U256};
    #[cfg(feature = "alloc")]
    use alloc::vec;

    impl_modulus!(
        Modulus,
        U256,
        "9CC24C5DF431A864188AB905AC751B727C9447A8E99E6366E1AD78A21E8D882B"
    );

    #[test]
    fn test_powmod_small_base() {
        let base = U256::from(105u64);
        let base_mod = const_residue!(base, Modulus);

        let exponent =
            U256::from_be_hex("77117F1273373C26C700D076B3F780074D03339F56DD0EFB60E7F58441FD3685");

        let res = base_mod.pow(&exponent);

        let expected =
            U256::from_be_hex("7B2CD7BDDD96C271E6F232F2F415BB03FE2A90BD6CCCEA5E94F1BFD064993766");
        assert_eq!(res.retrieve(), expected);
    }

    #[test]
    fn test_powmod_small_exponent() {
        let base =
            U256::from_be_hex("3435D18AA8313EBBE4D20002922225B53F75DC4453BB3EEC0378646F79B524A4");
        let base_mod = const_residue!(base, Modulus);

        let exponent = U256::from(105u64);

        let res = base_mod.pow(&exponent);

        let expected =
            U256::from_be_hex("89E2A4E99F649A5AE2C18068148C355CA927B34A3245C938178ED00D6EF218AA");
        assert_eq!(res.retrieve(), expected);
    }

    #[test]
    fn test_powmod() {
        let base =
            U256::from_be_hex("3435D18AA8313EBBE4D20002922225B53F75DC4453BB3EEC0378646F79B524A4");
        let base_mod = const_residue!(base, Modulus);

        let exponent =
            U256::from_be_hex("77117F1273373C26C700D076B3F780074D03339F56DD0EFB60E7F58441FD3685");

        let res = base_mod.pow(&exponent);

        let expected =
            U256::from_be_hex("3681BC0FEA2E5D394EB178155A127B0FD2EF405486D354251C385BDD51B9D421");
        assert_eq!(res.retrieve(), expected);
    }

    #[cfg(feature = "alloc")]
    #[test]
    fn test_multi_exp() {
        let base = U256::from(2u8);
        let base_mod = const_residue!(base, Modulus);

        let exponent = U256::from(33u8);

        let res =
            Residue::<Modulus, { U256::LIMBS }>::multi_exponentiate(vec![(base_mod, exponent)]);

        let expected =
            U256::from_be_hex("0000000000000000000000000000000000000000000000000000000200000000");

        assert_eq!(res.retrieve(), expected);

        let base2 =
            U256::from_be_hex("3435D18AA8313EBBE4D20002922225B53F75DC4453BB3EEC0378646F79B524A4");
        let base2_mod = const_residue!(base2, Modulus);

        let exponent2 =
            U256::from_be_hex("77117F1273373C26C700D076B3F780074D03339F56DD0EFB60E7F58441FD3685");

        let expected = base_mod.pow(&exponent) * base2_mod.pow(&exponent2);

        let res = Residue::<Modulus, { U256::LIMBS }>::multi_exponentiate(vec![
            (base_mod, exponent),
            (base2_mod, exponent2),
        ]);

        assert_eq!(res, expected);
    }
}
