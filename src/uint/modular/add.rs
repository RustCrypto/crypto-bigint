use crate::UInt;

pub(crate) const fn add_montgomery_form<const LIMBS: usize>(
    a: &UInt<LIMBS>,
    b: &UInt<LIMBS>,
    modulus: &UInt<LIMBS>,
) -> UInt<LIMBS> {
    a.add_mod(b, modulus)
}
