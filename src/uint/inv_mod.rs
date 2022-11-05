use subtle::{Choice, CtOption};

use super::UInt;
use crate::{Limb, Word};

impl<const LIMBS: usize> UInt<LIMBS> {
    /// Computes 1/`self` mod 2^k as specified in Algorithm 4 from
    /// A Secure Algorithm for Inversion Modulo 2k by
    /// Sadiel de la Fe and Carles Ferrer. See
    /// <https://www.mdpi.com/2410-387X/2/3/23>.
    ///
    /// Conditions: `self` < 2^k and `self` must be odd
    pub const fn inv_mod2k(&self, k: usize) -> Self {
        let mut x = Self::ZERO;
        let mut b = Self::ONE;
        let mut i = 0;

        while i < k {
            let mut x_i = Self::ZERO;
            let j = b.limbs[0].0 & 1;
            x_i.limbs[0] = Limb(j);
            x = x.bitor(&x_i.shl_vartime(i));

            let t = b.wrapping_sub(self);
            b = Self::ct_select(b, t, j.wrapping_neg()).shr_vartime(1);
            i += 1;
        }
        x
    }

    /// Computes the multiplicative inverse of `self` mod `modulus`. In other words `self^-1 mod modulus`. Returns `(inverse, 1...1)` if an inverse exists, otherwise `(undefined, 0...0)`. The algorithm is the same as in GMP 6.2.1's `mpn_sec_invert`.
    pub const fn inv_odd_mod(self, modulus: UInt<LIMBS>) -> (Self, Word) {
        debug_assert!(modulus.ct_is_odd() == Word::MAX);

        let mut a = self;

        let mut u = UInt::ONE;
        let mut v = UInt::ZERO;

        let mut b = modulus;

        // TODO: This can be lower if `self` is known to be small.
        let bit_size = 2 * LIMBS * 64;

        let mut m1hp = modulus;
        let (m1hp_new, carry) = m1hp.shr_1();
        debug_assert!(carry == Word::MAX);
        m1hp = m1hp_new.wrapping_add(&UInt::ONE);

        let mut i = 0;
        while i < bit_size {
            debug_assert!(b.ct_is_odd() == Word::MAX);

            let self_odd = a.ct_is_odd();

            // Set `self -= b` if `self` is odd.
            let (new_a, swap) = a.conditional_wrapping_sub(&b, self_odd);
            // Set `b += self` if `swap` is true.
            b = UInt::ct_select(b, b.wrapping_add(&new_a), swap);
            // Negate `self` if `swap` is true.
            a = new_a.conditional_wrapping_neg(swap);

            let (new_u, new_v) = UInt::ct_swap(u, v, swap);
            let (new_u, cy) = new_u.conditional_wrapping_sub(&new_v, self_odd);
            let (new_u, cyy) = new_u.conditional_wrapping_add(&modulus, cy);
            debug_assert!(cy == cyy);

            let (new_a, overflow) = a.shr_1();
            debug_assert!(overflow == 0);
            let (new_u, cy) = new_u.shr_1();
            let (new_u, cy) = new_u.conditional_wrapping_add(&m1hp, cy);
            debug_assert!(cy == 0);

            a = new_a;
            u = new_u;
            v = new_v;

            i += 1;
        }

        debug_assert!(a.ct_cmp(&UInt::ZERO) == 0);

        (v, b.ct_not_eq(&UInt::ONE) ^ Word::MAX)
    }

    /// Computes the multiplicative inverse of `self` mod `modulus`. In other words `self^-1 mod modulus`. Returns `None` if the inverse does not exist. The algorithm is the same as in GMP 6.2.1's `mpn_sec_invert`.
    pub fn inv_odd_mod_option(self, modulus: UInt<LIMBS>) -> CtOption<Self> {
        let (inverse, exists) = self.inv_odd_mod(modulus);
        CtOption::new(inverse, Choice::from((exists == Word::MAX) as u8))
    }
}

#[cfg(test)]
mod tests {
    use crate::{U1024, U256, U64};

    #[test]
    fn inv_mod2k() {
        let v = U256::from_be_slice(&[
            0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
            0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xfe,
            0xff, 0xff, 0xfc, 0x2f,
        ]);
        let e = U256::from_be_slice(&[
            0x36, 0x42, 0xe6, 0xfa, 0xea, 0xac, 0x7c, 0x66, 0x63, 0xb9, 0x3d, 0x3d, 0x6a, 0x0d,
            0x48, 0x9e, 0x43, 0x4d, 0xdc, 0x01, 0x23, 0xdb, 0x5f, 0xa6, 0x27, 0xc7, 0xf6, 0xe2,
            0x2d, 0xda, 0xca, 0xcf,
        ]);
        let a = v.inv_mod2k(256);
        assert_eq!(e, a);

        let v = U256::from_be_slice(&[
            0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
            0xff, 0xfe, 0xba, 0xae, 0xdc, 0xe6, 0xaf, 0x48, 0xa0, 0x3b, 0xbf, 0xd2, 0x5e, 0x8c,
            0xd0, 0x36, 0x41, 0x41,
        ]);
        let e = U256::from_be_slice(&[
            0x26, 0x17, 0x76, 0xf2, 0x9b, 0x6b, 0x10, 0x6c, 0x76, 0x80, 0xcf, 0x3e, 0xd8, 0x30,
            0x54, 0xa1, 0xaf, 0x5a, 0xe5, 0x37, 0xcb, 0x46, 0x13, 0xdb, 0xb4, 0xf2, 0x00, 0x99,
            0xaa, 0x77, 0x4e, 0xc1,
        ]);
        let a = v.inv_mod2k(256);
        assert_eq!(e, a);
    }

    #[test]
    fn test_invert() {
        let a = U1024::from_be_hex("000225E99153B467A5B451979A3F451DAEF3BF8D6C6521D2FA24BBB17F29544E347A412B065B75A351EA9719E2430D2477B11CC9CF9C1AD6EDEE26CB15F463F8BCC72EF87EA30288E95A48AA792226CEC959DCB0672D8F9D80A54CBBEA85CAD8382EC224DEB2F5784E62D0CC2F81C2E6AD14EBABE646D6764B30C32B87688985");
        let m = U1024::from_be_hex("D509E7854ABDC81921F669F1DC6F61359523F3949803E58ED4EA8BC16483DC6F37BFE27A9AC9EEA2969B357ABC5C0EE214BE16A7D4C58FC620D5B5A20AFF001AD198D3155E5799DC4EA76652D64983A7E130B5EACEBAC768D28D589C36EC749C558D0B64E37CD0775C0D0104AE7D98BA23C815185DD43CD8B16292FD94156767");

        let res = a.inv_odd_mod_option(m);

        let expected = U1024::from_be_hex("B03623284B0EBABCABD5C5881893320281460C0A8E7BF4BFDCFFCBCCBF436A55D364235C8171E46C7D21AAD0680676E57274A8FDA6D12768EF961CACDD2DAE5788D93DA5EB8EDC391EE3726CDCF4613C539F7D23E8702200CB31B5ED5B06E5CA3E520968399B4017BF98A864FABA2B647EFC4998B56774D4F2CB026BC024A336");
        assert_eq!(res.unwrap(), expected);
    }

    #[test]
    fn test_invert_small() {
        let a = U64::from(3u64);
        let m = U64::from(13u64);

        let res = a.inv_odd_mod_option(m);

        assert_eq!(U64::from(9u64), res.unwrap());
    }

    #[test]
    fn test_no_inverse_small() {
        let a = U64::from(14u64);
        let m = U64::from(49u64);

        let res = a.inv_odd_mod_option(m);

        assert!(res.is_none().unwrap_u8() == 1);
    }
}
