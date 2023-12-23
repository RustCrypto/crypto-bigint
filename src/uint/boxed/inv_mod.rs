//! [`BoxedUint`] modular inverse (i.e. reciprocal) operations.

use crate::{
    modular::BoxedBernsteinYangInverter, BoxedUint, ConstantTimeSelect, Integer, Inverter, Odd,
    PrecomputeInverter, PrecomputeInverterWithAdjuster,
};
use subtle::{Choice, ConstantTimeEq, ConstantTimeLess, CtOption};

impl BoxedUint {
    /// Computes the multiplicative inverse of `self` mod `modulus`.
    /// Returns `None` if an inverse does not exist.
    pub fn inv_mod(&self, modulus: &Odd<Self>) -> CtOption<Self> {
        modulus.precompute_inverter().invert(self)
    }

    /// Computes 1/`self` mod `2^k`.
    ///
    /// If the inverse does not exist (`k > 0` and `self` is even),
    /// returns `Choice::FALSE` as the second element of the tuple,
    /// otherwise returns `Choice::TRUE`.
    pub(crate) fn inv_mod2k(&self, k: u32) -> (Self, Choice) {
        let mut x = Self::zero_with_precision(self.bits_precision()); // keeps `x` during iterations
        let mut b = Self::one_with_precision(self.bits_precision()); // keeps `b_i` during iterations

        // The inverse exists either if `k` is 0 or if `self` is odd.
        let is_some = k.ct_eq(&0) | self.is_odd();

        for i in 0..self.bits_precision() {
            // Only iterations for i = 0..k need to change `x`,
            // the rest are dummy ones performed for the sake of constant-timeness.
            let within_range = i.ct_lt(&k);

            // X_i = b_i mod 2
            let x_i = b.limbs[0].0 & 1;
            let x_i_choice = Choice::from(x_i as u8);
            // b_{i+1} = (b_i - a * X_i) / 2
            b = Self::ct_select(&b, &b.wrapping_sub(self), x_i_choice).shr1();

            // Store the X_i bit in the result (x = x | (1 << X_i))
            // Don't change the result in dummy iterations.
            let x_i_choice = x_i_choice & within_range;
            x.set_bit(i, x_i_choice);
        }

        (x, is_some)
    }
}

/// Precompute a Bernstein-Yang inverter using `self` as the modulus.
impl PrecomputeInverter for Odd<BoxedUint> {
    type Inverter = BoxedBernsteinYangInverter;
    type Output = BoxedUint;

    fn precompute_inverter(&self) -> BoxedBernsteinYangInverter {
        Self::precompute_inverter_with_adjuster(self, &BoxedUint::one())
    }
}

/// Precompute a Bernstein-Yang inverter using `self` as the modulus.
impl PrecomputeInverterWithAdjuster<BoxedUint> for Odd<BoxedUint> {
    fn precompute_inverter_with_adjuster(
        &self,
        adjuster: &BoxedUint,
    ) -> BoxedBernsteinYangInverter {
        BoxedBernsteinYangInverter::new(self, adjuster)
    }
}

#[cfg(test)]
mod tests {
    use super::BoxedUint;
    use hex_literal::hex;

    #[test]
    fn inv_mod2k() {
        let v = BoxedUint::from_be_slice(
            &hex!("fffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2f"),
            256,
        )
        .unwrap();
        let e = BoxedUint::from_be_slice(
            &hex!("3642e6faeaac7c6663b93d3d6a0d489e434ddc0123db5fa627c7f6e22ddacacf"),
            256,
        )
        .unwrap();
        let (a, is_some) = v.inv_mod2k(256);
        assert_eq!(e, a);
        assert!(bool::from(is_some));

        let v = BoxedUint::from_be_slice(
            &hex!("fffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141"),
            256,
        )
        .unwrap();
        let e = BoxedUint::from_be_slice(
            &hex!("261776f29b6b106c7680cf3ed83054a1af5ae537cb4613dbb4f20099aa774ec1"),
            256,
        )
        .unwrap();
        let (a, is_some) = v.inv_mod2k(256);
        assert_eq!(e, a);
        assert!(bool::from(is_some));
    }
}
