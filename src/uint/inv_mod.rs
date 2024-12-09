use super::Uint;
use crate::{
    modular::SafeGcdInverter, ConstChoice, ConstCtOption, InvMod, Odd, PrecomputeInverter,
};
use subtle::CtOption;

impl<const LIMBS: usize> Uint<LIMBS> {
    /// Computes 1/`self` mod `2^k`.
    /// This method is constant-time w.r.t. `self` but not `k`.
    ///
    /// If the inverse does not exist (`k > 0` and `self` is even),
    /// returns `ConstChoice::FALSE` as the second element of the tuple,
    /// otherwise returns `ConstChoice::TRUE`.
    pub const fn inv_mod2k_vartime(&self, k: u32) -> ConstCtOption<Self> {
        // Using the Algorithm 3 from "A Secure Algorithm for Inversion Modulo 2k"
        // by Sadiel de la Fe and Carles Ferrer.
        // See <https://www.mdpi.com/2410-387X/2/3/23>.

        // Note that we are not using Alrgorithm 4, since we have a different approach
        // of enforcing constant-timeness w.r.t. `self`.

        let mut x = Self::ZERO; // keeps `x` during iterations
        let mut b = Self::ONE; // keeps `b_i` during iterations
        let mut i = 0;

        // The inverse exists either if `k` is 0 or if `self` is odd.
        let is_some = ConstChoice::from_u32_nonzero(k).not().or(self.is_odd());

        while i < k {
            // X_i = b_i mod 2
            let x_i = b.limbs[0].0 & 1;
            let x_i_choice = ConstChoice::from_word_lsb(x_i);
            // b_{i+1} = (b_i - a * X_i) / 2
            b = Self::select(&b, &b.wrapping_sub(self), x_i_choice).shr1();
            // Store the X_i bit in the result (x = x | (1 << X_i))
            let shifted = Uint::from_word(x_i)
                .overflowing_shl_vartime(i)
                .expect("shift within range");
            x = x.bitor(&shifted);

            i += 1;
        }

        ConstCtOption::new(x, is_some)
    }

    /// Computes 1/`self` mod `2^k`.
    ///
    /// If the inverse does not exist (`k > 0` and `self` is even),
    /// returns `ConstChoice::FALSE` as the second element of the tuple,
    /// otherwise returns `ConstChoice::TRUE`.
    pub const fn inv_mod2k(&self, k: u32) -> ConstCtOption<Self> {
        // This is the same algorithm as in `inv_mod2k_vartime()`,
        // but made constant-time w.r.t `k` as well.

        let mut x = Self::ZERO; // keeps `x` during iterations
        let mut b = Self::ONE; // keeps `b_i` during iterations
        let mut i = 0;

        // The inverse exists either if `k` is 0 or if `self` is odd.
        let is_some = ConstChoice::from_u32_nonzero(k).not().or(self.is_odd());

        while i < Self::BITS {
            // Only iterations for i = 0..k need to change `x`,
            // the rest are dummy ones performed for the sake of constant-timeness.
            let within_range = ConstChoice::from_u32_lt(i, k);

            // X_i = b_i mod 2
            let x_i = b.limbs[0].0 & 1;
            let x_i_choice = ConstChoice::from_word_lsb(x_i);
            // b_{i+1} = (b_i - self * X_i) / 2
            b = Self::select(&b, &b.wrapping_sub(self), x_i_choice).shr1();

            // Store the X_i bit in the result (x = x | (1 << X_i))
            // Don't change the result in dummy iterations.
            let x_i_choice = x_i_choice.and(within_range);
            x = x.set_bit(i, x_i_choice);

            i += 1;
        }

        ConstCtOption::new(x, is_some)
    }
}

impl<const LIMBS: usize, const UNSAT_LIMBS: usize> Uint<LIMBS>
where
    Odd<Self>: PrecomputeInverter<Inverter = SafeGcdInverter<LIMBS, UNSAT_LIMBS>>,
{
    /// Computes the multiplicative inverse of `self` mod `modulus`, where `modulus` is odd.
    pub const fn inv_odd_mod(&self, modulus: &Odd<Self>) -> ConstCtOption<Self> {
        SafeGcdInverter::<LIMBS, UNSAT_LIMBS>::new(modulus, &Uint::ONE).inv(self)
    }

    /// Computes the multiplicative inverse of `self` mod `modulus`.
    ///
    /// Returns some if an inverse exists, otherwise none.
    pub const fn inv_mod(&self, modulus: &Self) -> ConstCtOption<Self> {
        // Decompose `modulus = s * 2^k` where `s` is odd
        let k = modulus.trailing_zeros();
        let s = modulus.overflowing_shr(k).unwrap_or(Self::ZERO);

        // Decompose `self` into RNS with moduli `2^k` and `s` and calculate the inverses.
        // Using the fact that `(z^{-1} mod (m1 * m2)) mod m1 == z^{-1} mod m1`
        let s_is_odd = s.is_odd();
        let maybe_a = self.inv_odd_mod(&Odd(s)).and_choice(s_is_odd);

        let maybe_b = self.inv_mod2k(k);
        let is_some = maybe_a.is_some().and(maybe_b.is_some());

        // Unwrap to avoid mapping through ConstCtOptions.
        // if `a` or `b` don't exist, the returned ConstCtOption will be None anyway.
        let a = maybe_a.unwrap_or(Uint::ZERO);
        let b = maybe_b.unwrap_or(Uint::ZERO);

        // Restore from RNS:
        // self^{-1} = a mod s = b mod 2^k
        // => self^{-1} = a + s * ((b - a) * s^(-1) mod 2^k)
        // (essentially one step of the Garner's algorithm for recovery from RNS).

        // `s` is odd, so this always exists
        let m_odd_inv = s.inv_mod2k(k).expect("inverse mod 2^k exists");

        // This part is mod 2^k
        let shifted = Uint::ONE.overflowing_shl(k).unwrap_or(Self::ZERO);
        let mask = shifted.wrapping_sub(&Uint::ONE);
        let t = (b.wrapping_sub(&a).wrapping_mul(&m_odd_inv)).bitand(&mask);

        // Will not overflow since `a <= s - 1`, `t <= 2^k - 1`,
        // so `a + s * t <= s * 2^k - 1 == modulus - 1`.
        let result = a.wrapping_add(&s.wrapping_mul(&t));
        ConstCtOption::new(result, is_some)
    }
}

impl<const LIMBS: usize, const UNSAT_LIMBS: usize> InvMod for Uint<LIMBS>
where
    Odd<Self>: PrecomputeInverter<Inverter = SafeGcdInverter<LIMBS, UNSAT_LIMBS>>,
{
    fn inv_mod(&self, modulus: &Self) -> CtOption<Self> {
        self.inv_mod(modulus).into()
    }
}

#[cfg(test)]
mod tests {
    use crate::{U1024, U256, U64};

    #[test]
    fn inv_mod2k() {
        let v =
            U256::from_be_hex("fffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2f");
        let e =
            U256::from_be_hex("3642e6faeaac7c6663b93d3d6a0d489e434ddc0123db5fa627c7f6e22ddacacf");
        let a = v.inv_mod2k(256).unwrap();
        assert_eq!(e, a);

        let a = v.inv_mod2k_vartime(256).unwrap();
        assert_eq!(e, a);

        let v =
            U256::from_be_hex("fffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141");
        let e =
            U256::from_be_hex("261776f29b6b106c7680cf3ed83054a1af5ae537cb4613dbb4f20099aa774ec1");
        let a = v.inv_mod2k(256).unwrap();
        assert_eq!(e, a);

        let a = v.inv_mod2k_vartime(256).unwrap();
        assert_eq!(e, a);

        // Check that even if the number is >= 2^k, the inverse is still correct.

        let v =
            U256::from_be_hex("fffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141");
        let e =
            U256::from_be_hex("0000000000000000000000000000000000000000034613dbb4f20099aa774ec1");
        let a = v.inv_mod2k(90).unwrap();
        assert_eq!(e, a);

        let a = v.inv_mod2k_vartime(90).unwrap();
        assert_eq!(e, a);

        // An inverse of an even number does not exist.

        let a = U256::from(10u64).inv_mod2k(4);
        assert!(a.is_none().is_true_vartime());

        let a = U256::from(10u64).inv_mod2k_vartime(4);
        assert!(a.is_none().is_true_vartime());

        // A degenerate case. An inverse mod 2^0 == 1 always exists even for even numbers.

        let a = U256::from(10u64).inv_mod2k_vartime(0).unwrap();
        assert_eq!(a, U256::ZERO);
    }

    #[test]
    fn test_invert_odd() {
        let a = U1024::from_be_hex(concat![
            "000225E99153B467A5B451979A3F451DAEF3BF8D6C6521D2FA24BBB17F29544E",
            "347A412B065B75A351EA9719E2430D2477B11CC9CF9C1AD6EDEE26CB15F463F8",
            "BCC72EF87EA30288E95A48AA792226CEC959DCB0672D8F9D80A54CBBEA85CAD8",
            "382EC224DEB2F5784E62D0CC2F81C2E6AD14EBABE646D6764B30C32B87688985"
        ]);
        let m = U1024::from_be_hex(concat![
            "D509E7854ABDC81921F669F1DC6F61359523F3949803E58ED4EA8BC16483DC6F",
            "37BFE27A9AC9EEA2969B357ABC5C0EE214BE16A7D4C58FC620D5B5A20AFF001A",
            "D198D3155E5799DC4EA76652D64983A7E130B5EACEBAC768D28D589C36EC749C",
            "558D0B64E37CD0775C0D0104AE7D98BA23C815185DD43CD8B16292FD94156767"
        ])
        .to_odd()
        .unwrap();
        let expected = U1024::from_be_hex(concat![
            "B03623284B0EBABCABD5C5881893320281460C0A8E7BF4BFDCFFCBCCBF436A55",
            "D364235C8171E46C7D21AAD0680676E57274A8FDA6D12768EF961CACDD2DAE57",
            "88D93DA5EB8EDC391EE3726CDCF4613C539F7D23E8702200CB31B5ED5B06E5CA",
            "3E520968399B4017BF98A864FABA2B647EFC4998B56774D4F2CB026BC024A336"
        ]);

        let res = a.inv_odd_mod(&m).unwrap();
        assert_eq!(res, expected);

        // Even though it is less efficient, it still works
        let res = a.inv_mod(&m).unwrap();
        assert_eq!(res, expected);
    }

    #[test]
    fn test_invert_odd_no_inverse() {
        // 2^128 - 159, a prime
        let p1 =
            U256::from_be_hex("00000000000000000000000000000000ffffffffffffffffffffffffffffff61");
        // 2^128 - 173, a prime
        let p2 =
            U256::from_be_hex("00000000000000000000000000000000ffffffffffffffffffffffffffffff53");

        let m = p1.wrapping_mul(&p2).to_odd().unwrap();

        // `m` is a multiple of `p1`, so no inverse exists
        let res = p1.inv_odd_mod(&m);
        assert!(res.is_none().is_true_vartime());
    }

    #[test]
    fn test_invert_even() {
        let a = U1024::from_be_hex(concat![
            "000225E99153B467A5B451979A3F451DAEF3BF8D6C6521D2FA24BBB17F29544E",
            "347A412B065B75A351EA9719E2430D2477B11CC9CF9C1AD6EDEE26CB15F463F8",
            "BCC72EF87EA30288E95A48AA792226CEC959DCB0672D8F9D80A54CBBEA85CAD8",
            "382EC224DEB2F5784E62D0CC2F81C2E6AD14EBABE646D6764B30C32B87688985"
        ]);
        let m = U1024::from_be_hex(concat![
            "D509E7854ABDC81921F669F1DC6F61359523F3949803E58ED4EA8BC16483DC6F",
            "37BFE27A9AC9EEA2969B357ABC5C0EE214BE16A7D4C58FC620D5B5A20AFF001A",
            "D198D3155E5799DC4EA76652D64983A7E130B5EACEBAC768D28D589C36EC749C",
            "558D0B64E37CD0775C0D0104AE7D98BA23C815185DD43CD8B16292FD94156000"
        ]);
        let expected = U1024::from_be_hex(concat![
            "1EBF391306817E1BC610E213F4453AD70911CCBD59A901B2A468A4FC1D64F357",
            "DBFC6381EC5635CAA664DF280028AF4651482C77A143DF38D6BFD4D64B6C0225",
            "FC0E199B15A64966FB26D88A86AD144271F6BDCD3D63193AB2B3CC53B99F21A3",
            "5B9BFAE5D43C6BC6E7A9856C71C7318C76530E9E5AE35882D5ABB02F1696874D",
        ]);

        let res = a.inv_mod(&m).unwrap();
        assert_eq!(res, expected);
    }

    #[test]
    fn test_invert_small() {
        let a = U64::from(3u64);
        let m = U64::from(13u64).to_odd().unwrap();

        let res = a.inv_odd_mod(&m).unwrap();
        assert_eq!(U64::from(9u64), res);
    }

    #[test]
    fn test_no_inverse_small() {
        let a = U64::from(14u64);
        let m = U64::from(49u64).to_odd().unwrap();

        let res = a.inv_odd_mod(&m);
        assert!(res.is_none().is_true_vartime());
    }
}
