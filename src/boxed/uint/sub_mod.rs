//! [`BoxedUint`] modular subtraction operations.

use crate::{BoxedUint, Limb, SubMod};

impl BoxedUint {
    /// Computes `self - rhs mod p`.
    ///
    /// Assumes `self - rhs` as unbounded signed integer is in `[-p, p)`.
    pub fn sub_mod(&self, rhs: &Self, p: &Self) -> Self {
        debug_assert_eq!(self.nlimbs(), p.nlimbs());
        debug_assert_eq!(rhs.nlimbs(), p.nlimbs());
        debug_assert!(self < p);
        debug_assert!(rhs < p);

        let (out, borrow) = self.sbb(rhs, Limb::ZERO);

        // If underflow occurred on the final limb, borrow = 0xfff...fff, otherwise
        // borrow = 0x000...000. Thus, we use it as a mask to conditionally add the modulus.
        let mask = Self::from_words(vec![borrow.0; p.nlimbs()]);

        out.wrapping_add(&p.bitand(&mask))
    }
}

impl SubMod for BoxedUint {
    type Output = Self;

    fn sub_mod(&self, rhs: &Self, p: &Self) -> Self {
        self.sub_mod(rhs, p)
    }
}

#[cfg(test)]
mod tests {
    use super::BoxedUint;
    use hex_literal::hex;

    #[test]
    fn sub_mod_nist_p256() {
        let a = BoxedUint::from_be_slice(
            &hex!("1a2472fde50286541d97ca6a3592dd75beb9c9646e40c511b82496cfc3926956"),
            256,
        )
        .unwrap();
        let b = BoxedUint::from_be_slice(
            &hex!("d5777c45019673125ad240f83094d4252d829516fac8601ed01979ec1ec1a251"),
            256,
        )
        .unwrap();
        let n = BoxedUint::from_be_slice(
            &hex!("ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551"),
            256,
        )
        .unwrap();

        let actual = a.sub_mod(&b, &n);
        let expected = BoxedUint::from_be_slice(
            &hex!("44acf6b7e36c1342c2c5897204fe09504e1e2efb1a900377dbc4e7a6a133ec56"),
            256,
        )
        .unwrap();

        assert_eq!(expected, actual);
    }
}
