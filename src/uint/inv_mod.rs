use subtle::ConditionallySelectable;

use super::UInt;
use crate::{Integer, Limb, Wrapping};

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

    pub fn inv_mod(mut self, modulus: &UInt<LIMBS>) -> Option<UInt<LIMBS>> {
        debug_assert!(modulus.is_odd().unwrap_u8() == 1);

        let mut u = UInt::ONE;
        let mut v = UInt::ZERO;

        let mut b = *modulus;

        // TODO: This can be lower if `self` is known to be small.
        let bit_size = 2 * LIMBS * 64;

        let mut m1hp = modulus.clone();
        let carry = m1hp.shr_1();
        debug_assert!(carry.unwrap_u8() == 1);
        let mut m1hp = Wrapping(m1hp);
        m1hp += &Wrapping(UInt::ONE);

        for _ in 0..bit_size {
            debug_assert!(b.is_odd().unwrap_u8() == 1);

            let self_odd = self.is_odd();

            // Set `self -= b` if `self` is odd.
            let swap = self.conditional_wrapping_sub(&b, self_odd);
            // Set `b += self` if `swap` is true.
            b = UInt::conditional_select(&b, &(b.wrapping_add(&self)), swap);
            // Negate `self` if `swap` is true.
            self = self.conditional_wrapping_neg(swap);

            UInt::conditional_swap(&mut u, &mut v, swap);
            let cy = u.conditional_wrapping_sub(&v, self_odd);
            let cyy = u.conditional_wrapping_add(modulus, cy);
            debug_assert_eq!(cy.unwrap_u8(), cyy.unwrap_u8());

            let overflow = self.shr_1();
            debug_assert!(overflow.unwrap_u8() == 0);
            let cy = u.shr_1();
            let cy = u.conditional_wrapping_add(&m1hp.0, cy);
            debug_assert!(cy.unwrap_u8() == 0);
        }

        debug_assert_eq!(self, UInt::ZERO);

        if b != UInt::ONE {
            None
        } else {
            Some(v)
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::U256;

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
}
