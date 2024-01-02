//! [`BoxedUint`] modular multiplication operations.

use crate::{
    modular::{BoxedMontyForm, BoxedMontyParams},
    primitives::mul_rem,
    BoxedUint, Limb, MulMod, Odd, WideWord, Word,
};

impl BoxedUint {
    /// Computes `self * rhs mod p` for odd `p`.
    ///
    /// Panics if `p` is even.
    // TODO(tarcieri): support for even `p`?
    pub fn mul_mod(&self, rhs: &BoxedUint, p: &BoxedUint) -> BoxedUint {
        // NOTE: the overhead of converting to Montgomery form to perform this operation and then
        // immediately converting out of Montgomery form after just a single operation is likely to
        // be higher than other possible implementations of this function, such as using a
        // Barrett reduction instead.
        //
        // It's worth potentially exploring other approaches to improve efficiency.
        match Odd::new(p.clone()).into() {
            Some(p) => {
                let params = BoxedMontyParams::new(p);
                let lhs = BoxedMontyForm::new(self.clone(), params.clone());
                let rhs = BoxedMontyForm::new(rhs.clone(), params);
                let ret = lhs * rhs;
                ret.retrieve()
            }
            None => todo!("even moduli are currently unsupported"),
        }
    }

    /// Computes `self * rhs mod p` for the special modulus
    /// `p = MAX+1-c` where `c` is small enough to fit in a single [`Limb`].
    ///
    /// For the modulus reduction, this function implements Algorithm 14.47 from
    /// the "Handbook of Applied Cryptography", by A. Menezes, P. van Oorschot,
    /// and S. Vanstone, CRC Press, 1996.
    pub fn mul_mod_special(&self, rhs: &Self, c: Limb) -> Self {
        debug_assert_eq!(self.bits_precision(), rhs.bits_precision());

        // We implicitly assume `LIMBS > 0`, because `Uint<0>` doesn't compile.
        // Still the case `LIMBS == 1` needs special handling.
        if self.nlimbs() == 1 {
            let reduced = mul_rem(self.limbs[0].0, rhs.limbs[0].0, Word::MIN.wrapping_sub(c.0));
            return Self::from(reduced);
        }

        let product = self.mul(rhs);
        let (lo_words, hi_words) = product.limbs.split_at(self.nlimbs());
        let lo = BoxedUint::from(lo_words);
        let hi = BoxedUint::from(hi_words);

        // Now use Algorithm 14.47 for the reduction
        let (lo, carry) = mac_by_limb(&lo, &hi, c, Limb::ZERO);

        let (lo, carry) = {
            let rhs = (carry.0 + 1) as WideWord * c.0 as WideWord;
            lo.adc(&Self::from(rhs), Limb::ZERO)
        };

        let (lo, _) = {
            let rhs = carry.0.wrapping_sub(1) & c.0;
            lo.sbb(&Self::from(rhs), Limb::ZERO)
        };

        lo
    }
}

impl MulMod for BoxedUint {
    type Output = Self;

    fn mul_mod(&self, rhs: &Self, p: &Self) -> Self {
        self.mul_mod(rhs, p)
    }
}

/// Computes `a + (b * c) + carry`, returning the result along with the new carry.
fn mac_by_limb(a: &BoxedUint, b: &BoxedUint, c: Limb, carry: Limb) -> (BoxedUint, Limb) {
    let mut a = a.clone();
    let mut carry = carry;

    for i in 0..a.nlimbs() {
        let (n, c) = a.limbs[i].mac(b.limbs[i], c, carry);
        a.limbs[i] = n;
        carry = c;
    }

    (a, carry)
}

#[cfg(all(test, feature = "rand"))]
mod tests {
    use crate::{Limb, NonZero, Random, RandomMod, Uint};
    use rand_core::SeedableRng;

    macro_rules! test_mul_mod_special {
        ($size:expr, $test_name:ident) => {
            #[test]
            fn $test_name() {
                let mut rng = rand_chacha::ChaCha8Rng::seed_from_u64(1);
                let moduli = [
                    NonZero::<Limb>::random(&mut rng),
                    NonZero::<Limb>::random(&mut rng),
                ];

                for special in &moduli {
                    let p =
                        &NonZero::new(Uint::ZERO.wrapping_sub(&Uint::from(special.get()))).unwrap();

                    let minus_one = p.wrapping_sub(&Uint::ONE);

                    let base_cases = [
                        (Uint::ZERO, Uint::ZERO, Uint::ZERO),
                        (Uint::ONE, Uint::ZERO, Uint::ZERO),
                        (Uint::ZERO, Uint::ONE, Uint::ZERO),
                        (Uint::ONE, Uint::ONE, Uint::ONE),
                        (minus_one, minus_one, Uint::ONE),
                        (minus_one, Uint::ONE, minus_one),
                        (Uint::ONE, minus_one, minus_one),
                    ];
                    for (a, b, c) in &base_cases {
                        let x = a.mul_mod_special(&b, *special.as_ref());
                        assert_eq!(*c, x, "{} * {} mod {} = {} != {}", a, b, p, x, c);
                    }

                    for _i in 0..100 {
                        let a = Uint::<$size>::random_mod(&mut rng, p);
                        let b = Uint::<$size>::random_mod(&mut rng, p);

                        let c = a.mul_mod_special(&b, *special.as_ref());
                        assert!(c < **p, "not reduced: {} >= {} ", c, p);

                        let expected = {
                            let (lo, hi) = a.split_mul(&b);
                            let mut prod = Uint::<{ 2 * $size }>::ZERO;
                            prod.limbs[..$size].clone_from_slice(&lo.limbs);
                            prod.limbs[$size..].clone_from_slice(&hi.limbs);
                            let mut modulus = Uint::ZERO;
                            modulus.limbs[..$size].clone_from_slice(&p.as_ref().limbs);
                            let reduced = prod.rem_vartime(&NonZero::new(modulus).unwrap());
                            let mut expected = Uint::ZERO;
                            expected.limbs[..].clone_from_slice(&reduced.limbs[..$size]);
                            expected
                        };
                        assert_eq!(c, expected, "incorrect result");
                    }
                }
            }
        };
    }

    test_mul_mod_special!(1, mul_mod_special_1);
    test_mul_mod_special!(2, mul_mod_special_2);
    test_mul_mod_special!(3, mul_mod_special_3);
    test_mul_mod_special!(4, mul_mod_special_4);
    test_mul_mod_special!(5, mul_mod_special_5);
    test_mul_mod_special!(6, mul_mod_special_6);
    test_mul_mod_special!(7, mul_mod_special_7);
    test_mul_mod_special!(8, mul_mod_special_8);
    test_mul_mod_special!(9, mul_mod_special_9);
    test_mul_mod_special!(10, mul_mod_special_10);
    test_mul_mod_special!(11, mul_mod_special_11);
    test_mul_mod_special!(12, mul_mod_special_12);
}
