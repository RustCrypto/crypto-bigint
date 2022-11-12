use crate::{Limb, UInt, Word};

use super::mul::{mul_montgomery_form, square_montgomery_form};

pub trait PowResidue<const LIMBS: usize>
where
    Self: Sized,
{
    /// Computes the (reduced) exponentiation of a residue.
    fn pow(self, exponent: &UInt<LIMBS>) -> Self {
        self.pow_specific(exponent, LIMBS * Word::BITS as usize)
    }

    /// Computes the (reduced) exponentiation of a residue, here `exponent_bits` represents the number of bits to take into account for the exponent. Note that this value is leaked in the time pattern.
    fn pow_specific(self, exponent: &UInt<LIMBS>, exponent_bits: usize) -> Self;
}

/// Performs modular exponentiation using Montgomery's ladder. `exponent_bits` represents the number of bits to take into account for the exponent. Note that this value is leaked in the time pattern.
pub const fn pow_montgomery_form<const LIMBS: usize>(
    x: UInt<LIMBS>,
    exponent: &UInt<LIMBS>,
    exponent_bits: usize,
    modulus: UInt<LIMBS>,
    r: UInt<LIMBS>,
    mod_neg_inv: Limb,
) -> UInt<LIMBS> {
    let mut x1: UInt<LIMBS> = r;
    let mut x2: UInt<LIMBS> = x;

    // Shift the exponent all the way to the left so the leftmost bit is the MSB of the `UInt`
    let mut n: UInt<LIMBS> = exponent.shl_vartime((LIMBS * Word::BITS as usize) - exponent_bits);

    let mut i = 0;
    while i < exponent_bits {
        // Peel off one bit at a time from the left side
        let (next_n, overflow) = n.shl_1();
        n = next_n;

        let mut product: UInt<LIMBS> = x1;
        product = mul_montgomery_form(&product, &x2, modulus, mod_neg_inv);

        let mut square = UInt::ct_select(x1, x2, overflow);
        square = square_montgomery_form(&square, modulus, mod_neg_inv);

        x1 = UInt::<LIMBS>::ct_select(square, product, overflow);
        x2 = UInt::<LIMBS>::ct_select(product, square, overflow);

        i += 1;
    }

    x1
}
