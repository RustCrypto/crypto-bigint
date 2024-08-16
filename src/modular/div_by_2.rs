#[cfg(feature = "alloc")]
use crate::{BoxedUint, ConstantTimeSelect};
use crate::{Odd, Uint};

pub(crate) const fn div_by_2<const LIMBS: usize>(
    a: &Uint<LIMBS>,
    modulus: &Odd<Uint<LIMBS>>,
) -> Uint<LIMBS> {
    // We are looking for such `b` that `b + b = a mod modulus`.
    // Two possibilities:
    // - if `a` is even, we can just divide by 2;
    // - if `a` is odd, we divide `(a + modulus)` by 2.
    // To stay within the modulus we open the parentheses turning it into `a / 2 + modulus / 2 + 1`
    // ("+1" because both `a` and `modulus` are odd, we lose 0.5 in each integer division).
    // This will not overflow, so we can just use wrapping operations.

    // Note that this also works if `a` is a Montgomery representation modulo `modulus`
    // of some integer `x`.
    // If `b + b = a mod modulus` it means that `y + y = x mod modulus` where `y` is the integer
    // whose Montgomery representation is `b`.

    let (half, is_odd) = a.shr1_with_carry();
    let half_modulus = modulus.0.shr1();

    let if_even = half;
    let if_odd = half
        .wrapping_add(&half_modulus)
        .wrapping_add(&Uint::<LIMBS>::ONE);

    Uint::<LIMBS>::select(&if_even, &if_odd, is_odd)
}

#[cfg(feature = "alloc")]
pub(crate) fn div_by_2_boxed(a: &BoxedUint, modulus: &Odd<BoxedUint>) -> BoxedUint {
    debug_assert_eq!(a.bits_precision(), modulus.bits_precision());

    let (mut half, is_odd) = a.shr1_with_carry();
    let half_modulus = modulus.shr1();

    let if_odd = half
        .wrapping_add(&half_modulus)
        .wrapping_add(&BoxedUint::one_with_precision(a.bits_precision()));

    half.ct_assign(&if_odd, is_odd);

    half
}
