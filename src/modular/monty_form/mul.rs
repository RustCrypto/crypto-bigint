//! Multiplications between integers in Montgomery form with a modulus set at runtime.

use super::MontyForm;
use crate::{
    MontyMultiplier, Square, SquareAssign,
    modular::{
        MontyParams,
        mul::{mul_montgomery_form, square_montgomery_form, square_repeat_montgomery_form},
    },
};
use core::ops::{Mul, MulAssign};

impl<const LIMBS: usize> MontyForm<LIMBS> {
    /// Multiplies by `rhs`.
    #[must_use]
    pub const fn mul(&self, rhs: &Self) -> Self {
        Self {
            montgomery_form: mul_montgomery_form(
                &self.montgomery_form,
                &rhs.montgomery_form,
                &self.params.modulus,
                self.params.mod_neg_inv(),
            ),
            params: self.params,
        }
    }

    /// Computes the (reduced) square.
    #[must_use]
    pub const fn square(&self) -> Self {
        Self {
            montgomery_form: square_montgomery_form(
                &self.montgomery_form,
                &self.params.modulus,
                self.params.mod_neg_inv(),
            ),
            params: self.params,
        }
    }

    /// Computes the reduced product `self^2n`.
    ///
    /// This method is variable time in `n` only.
    #[must_use]
    pub const fn square_repeat_vartime(&self, n: u32) -> Self {
        Self {
            montgomery_form: square_repeat_montgomery_form::<LIMBS>(
                &self.montgomery_form,
                n,
                &self.params.modulus,
                self.params.mod_neg_inv(),
            ),
            params: self.params,
        }
    }
}

impl<const LIMBS: usize> Mul<&MontyForm<LIMBS>> for &MontyForm<LIMBS> {
    type Output = MontyForm<LIMBS>;
    fn mul(self, rhs: &MontyForm<LIMBS>) -> MontyForm<LIMBS> {
        debug_assert_eq!(self.params, rhs.params);
        self.mul(rhs)
    }
}

impl<const LIMBS: usize> Mul<MontyForm<LIMBS>> for &MontyForm<LIMBS> {
    type Output = MontyForm<LIMBS>;
    #[allow(clippy::op_ref)]
    fn mul(self, rhs: MontyForm<LIMBS>) -> MontyForm<LIMBS> {
        self * &rhs
    }
}

impl<const LIMBS: usize> Mul<&MontyForm<LIMBS>> for MontyForm<LIMBS> {
    type Output = MontyForm<LIMBS>;
    #[allow(clippy::op_ref)]
    fn mul(self, rhs: &MontyForm<LIMBS>) -> MontyForm<LIMBS> {
        &self * rhs
    }
}

impl<const LIMBS: usize> Mul<MontyForm<LIMBS>> for MontyForm<LIMBS> {
    type Output = MontyForm<LIMBS>;
    fn mul(self, rhs: MontyForm<LIMBS>) -> MontyForm<LIMBS> {
        &self * &rhs
    }
}

impl<const LIMBS: usize> MulAssign<&MontyForm<LIMBS>> for MontyForm<LIMBS> {
    fn mul_assign(&mut self, rhs: &MontyForm<LIMBS>) {
        *self = *self * rhs;
    }
}

impl<const LIMBS: usize> MulAssign<MontyForm<LIMBS>> for MontyForm<LIMBS> {
    fn mul_assign(&mut self, rhs: MontyForm<LIMBS>) {
        *self *= &rhs;
    }
}

impl<const LIMBS: usize> Square for MontyForm<LIMBS> {
    fn square(&self) -> Self {
        MontyForm::square(self)
    }
}

impl<const LIMBS: usize> SquareAssign for MontyForm<LIMBS> {
    fn square_assign(&mut self) {
        *self = self.square();
    }
}

#[derive(Debug, Clone, Copy)]
pub struct DynMontyMultiplier<'a, const LIMBS: usize>(&'a MontyParams<LIMBS>);

impl<'a, const LIMBS: usize> From<&'a MontyParams<LIMBS>> for DynMontyMultiplier<'a, LIMBS> {
    fn from(source: &'a MontyParams<LIMBS>) -> Self {
        Self(source)
    }
}

impl<'a, const LIMBS: usize> MontyMultiplier<'a> for DynMontyMultiplier<'a, LIMBS> {
    type Monty = MontyForm<LIMBS>;

    /// Performs a Montgomery multiplication, assigning a fully reduced result to `lhs`.
    fn mul_assign(&mut self, lhs: &mut Self::Monty, rhs: &Self::Monty) {
        let product = mul_montgomery_form(
            &lhs.montgomery_form,
            &rhs.montgomery_form,
            &self.0.modulus,
            self.0.mod_neg_inv(),
        );
        lhs.montgomery_form = product;
    }

    /// Performs a Montgomery squaring, assigning a fully reduced result to `lhs`.
    fn square_assign(&mut self, lhs: &mut Self::Monty) {
        let product =
            square_montgomery_form(&lhs.montgomery_form, &self.0.modulus, self.0.mod_neg_inv());
        lhs.montgomery_form = product;
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        Odd, U256,
        modular::{MontyForm, MontyParams},
    };

    const PARAMS: MontyParams<{ U256::LIMBS }> =
        MontyParams::new_vartime(Odd::<U256>::from_be_hex(
            "ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551",
        ));
    const N: U256 =
        U256::from_be_hex("14117F1273373C26C700D076B3F780074D03339F56DD0EFB60E7F58441FD3685");
    const N_MOD: MontyForm<{ U256::LIMBS }> = MontyForm::new(&N, &PARAMS);

    #[test]
    fn test_mul_zero() {
        let res = N_MOD.mul(&MontyForm::zero(PARAMS));
        let expected = U256::ZERO;
        assert_eq!(res.retrieve(), expected);
    }

    #[test]
    fn test_mul_one() {
        let res = N_MOD.mul(&MontyForm::one(PARAMS));
        assert_eq!(res.retrieve(), N);
    }

    #[test]
    fn test_mul_eq_add() {
        let res = N_MOD.mul(&MontyForm::new(&U256::from(2u8), &PARAMS));
        assert_eq!(res, N_MOD.add(&N_MOD));
    }

    #[test]
    fn test_square_eq_mul() {
        let res = N_MOD.square();
        let expected = N_MOD.mul(&N_MOD);
        assert_eq!(res, expected);
    }

    #[test]
    fn test_square_repeat() {
        let res = N_MOD.square_repeat_vartime(0);
        assert_eq!(res, N_MOD);

        let res = N_MOD.square_repeat_vartime(1);
        assert_eq!(res, N_MOD.square());

        let res = N_MOD.square_repeat_vartime(5);
        let expected = N_MOD.square().square().square().square().square();
        assert_eq!(res, expected);
    }
}
