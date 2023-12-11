//! [`BoxedUint`] modular inverse (i.e. reciprocal) operations.

use crate::BoxedUint;
use subtle::{Choice, ConstantTimeEq, ConstantTimeLess, CtOption};

impl BoxedUint {
    /// Computes the multiplicative inverse of `self` mod `modulus`.
    /// Returns `None` if an inverse does not exist.
    pub fn inv_mod(&self, modulus: &Self) -> CtOption<Self> {
        debug_assert_eq!(self.bits_precision(), modulus.bits_precision());

        // Decompose `modulus = s * 2^k` where `s` is odd
        let k = modulus.trailing_zeros();
        let s = modulus >> k;

        // Decompose `self` into RNS with moduli `2^k` and `s` and calculate the inverses.
        // Using the fact that `(z^{-1} mod (m1 * m2)) mod m1 == z^{-1} mod m1`
        let (a, a_is_some) = self.inv_odd_mod(&s);
        let (b, b_is_some) = self.inv_mod2k(k);

        // Restore from RNS:
        // self^{-1} = a mod s = b mod 2^k
        // => self^{-1} = a + s * ((b - a) * s^(-1) mod 2^k)
        // (essentially one step of the Garner's algorithm for recovery from RNS).

        let (m_odd_inv, _is_some) = s.inv_mod2k(k); // `s` is odd, so this always exists

        // This part is mod 2^k
        let mask = (Self::one() << k).wrapping_sub(&Self::one());
        let t = (b.wrapping_sub(&a).wrapping_mul(&m_odd_inv)).bitand(&mask);

        // Will not overflow since `a <= s - 1`, `t <= 2^k - 1`,
        // so `a + s * t <= s * 2^k - 1 == modulus - 1`.
        let result = a.wrapping_add(&s.wrapping_mul(&t));
        CtOption::new(result, a_is_some & b_is_some)
    }

    /// Computes 1/`self` mod `2^k`.
    ///
    /// If the inverse does not exist (`k > 0` and `self` is even),
    /// returns `CtChoice::FALSE` as the second element of the tuple,
    /// otherwise returns `CtChoice::TRUE`.
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
            b = Self::conditional_select(&b, &b.wrapping_sub(self), x_i_choice).shr1();

            // Store the X_i bit in the result (x = x | (1 << X_i))
            // Don't change the result in dummy iterations.
            let x_i_choice = x_i_choice & within_range;
            x.set_bit(i, x_i_choice);
        }

        (x, is_some)
    }

    /// Computes the multiplicative inverse of `self` mod `modulus`, where `modulus` is odd.
    /// Returns `None` if an inverse does not exist.
    pub(crate) fn inv_odd_mod(&self, modulus: &Self) -> (Self, Choice) {
        self.inv_odd_mod_bounded(modulus, self.bits_precision(), modulus.bits_precision())
    }

    /// Computes the multiplicative inverse of `self` mod `modulus`, where `modulus` is odd.
    /// In other words `self^-1 mod modulus`.
    ///
    /// `bits` and `modulus_bits` are the bounds on the bit size
    /// of `self` and `modulus`, respectively.
    ///
    /// (the inversion speed will be proportional to `bits + modulus_bits`).
    /// The second element of the tuple is the truthy value
    /// if `modulus` is odd and an inverse exists, otherwise it is a falsy value.
    ///
    /// **Note:** variable time in `bits` and `modulus_bits`.
    ///
    /// The algorithm is the same as in GMP 6.2.1's `mpn_sec_invert`.
    fn inv_odd_mod_bounded(&self, modulus: &Self, bits: u32, modulus_bits: u32) -> (Self, Choice) {
        debug_assert_eq!(self.bits_precision(), modulus.bits_precision());

        let bits_precision = self.bits_precision();

        let mut a = self.clone();
        let mut u = Self::one_with_precision(bits_precision);
        let mut v = Self::zero_with_precision(bits_precision);
        let mut b = modulus.clone();

        // `bit_size` can be anything >= `self.bits()` + `modulus.bits()`, setting to the minimum.
        let bit_size = bits + modulus_bits;

        let m1hp = modulus
            .shr1()
            .wrapping_add(&Self::one_with_precision(bits_precision));

        let modulus_is_odd = modulus.is_odd();

        for _ in 0..bit_size {
            // A sanity check that `b` stays odd. Only matters if `modulus` was odd to begin with,
            // otherwise this whole thing produces nonsense anyway.
            debug_assert!(bool::from(!modulus_is_odd | b.is_odd()));

            let self_odd = a.is_odd();

            // Set `self -= b` if `self` is odd.
            let swap = a.conditional_sbb_assign(&b, self_odd);
            // Set `b += self` if `swap` is true.
            b = Self::conditional_select(&b, &b.wrapping_add(&a), swap);
            // Negate `self` if `swap` is true.
            a = a.conditional_wrapping_neg(swap);

            let mut new_u = u.clone();
            let mut new_v = v.clone();
            Self::conditional_swap(&mut new_u, &mut new_v, swap);
            let cy = new_u.conditional_sbb_assign(&new_v, self_odd);
            let cyy = new_u.conditional_adc_assign(modulus, cy);
            debug_assert!(bool::from(cy.ct_eq(&cyy)));

            let (new_a, carry) = a.shr1_with_carry();
            debug_assert!(bool::from(!modulus_is_odd | !carry));
            let (mut new_u, cy) = new_u.shr1_with_carry();
            let cy = new_u.conditional_adc_assign(&m1hp, cy);
            debug_assert!(bool::from(!modulus_is_odd | !cy));

            a = new_a;
            u = new_u;
            v = new_v;
        }

        debug_assert!(bool::from(!modulus_is_odd | a.is_zero()));
        (v, b.is_one() & modulus_is_odd)
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
