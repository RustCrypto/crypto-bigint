use crate::UInt;

pub(crate) const fn sub_montgomery_form<const LIMBS: usize>(
    a: &UInt<LIMBS>,
    b: &UInt<LIMBS>,
    modulus: &UInt<LIMBS>,
) -> UInt<LIMBS> {
    a.sub_mod(b, modulus)
}
