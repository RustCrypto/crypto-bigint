//! [`BoxedUint`] modular inverse (i.e. reciprocal) operations.

use crate::{BoxedUint, Word};
use subtle::{Choice, ConstantTimeLess};

impl BoxedUint {
    /// Computes 1/`self` mod `2^k`.
    ///
    /// Conditions: `self` < 2^k and `self` must be odd
    pub fn inv_mod2k(&self, k: usize) -> Self {
        // This is the same algorithm as in `inv_mod2k_vartime()`,
        // but made constant-time w.r.t `k` as well.

        let mut x = Self::zero_with_precision(self.bits_precision()); // keeps `x` during iterations
        let mut b = Self::one_with_precision(self.bits_precision()); // keeps `b_i` during iterations

        for i in 0..self.bits_precision() {
            // Only iterations for i = 0..k need to change `x`,
            // the rest are dummy ones performed for the sake of constant-timeness.
            let within_range = (i as Word).ct_lt(&(k as Word));

            // X_i = b_i mod 2
            let x_i = b.limbs[0].0 & 1;
            let x_i_choice = Choice::from(x_i as u8);
            // b_{i+1} = (b_i - a * X_i) / 2
            b = Self::conditional_select(&b, &b.wrapping_sub(self), x_i_choice).shr_vartime(1);

            // Store the X_i bit in the result (x = x | (1 << X_i))
            // Don't change the result in dummy iterations.
            let x_i_choice = x_i_choice & within_range;
            x.set_bit(i, x_i_choice);
        }

        x
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
        let a = v.inv_mod2k(256);
        assert_eq!(e, a);

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
        let a = v.inv_mod2k(256);
        assert_eq!(e, a);
    }
}
