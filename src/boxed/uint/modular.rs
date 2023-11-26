//! Modular arithmetic support for [`BoxedUint`].

use super::BoxedUint;
use crate::{modular::reduction::montgomery_reduction_core, Limb};

#[allow(dead_code)]
pub(crate) fn mul_montgomery_form(
    a: &BoxedUint,
    b: &BoxedUint,
    modulus: &BoxedUint,
    mod_neg_inv: Limb,
) -> BoxedUint {
    debug_assert_eq!(a.nlimbs(), modulus.nlimbs());
    debug_assert_eq!(b.nlimbs(), modulus.nlimbs());

    let mut product = a.mul_wide(b);
    let (lower, upper) = product.limbs.split_at_mut(modulus.nlimbs());
    let meta_carry = montgomery_reduction_core(lower, upper, &modulus.limbs, mod_neg_inv);
    let ret = BoxedUint::from(&*upper);

    #[cfg(feature = "zeroize")]
    zeroize::Zeroize::zeroize(&mut product);

    ret.sub_mod_with_carry(meta_carry, modulus, modulus)
}
