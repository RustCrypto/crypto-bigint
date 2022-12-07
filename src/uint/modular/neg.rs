use crate::UInt;

pub(crate) const fn neg_montgomery_form<const LIMBS: usize>(
    a: &UInt<LIMBS>,
    modulus: &UInt<LIMBS>,
) -> UInt<LIMBS> {
    a.neg_mod(modulus)
}
