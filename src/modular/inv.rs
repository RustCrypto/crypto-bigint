use crate::{modular::reduction::montgomery_reduction, ConstCtOption, Limb, Uint};

pub const fn inv_montgomery_form<const LIMBS: usize>(
    x: &Uint<LIMBS>,
    modulus: &Uint<LIMBS>,
    r3: &Uint<LIMBS>,
    mod_neg_inv: Limb,
) -> ConstCtOption<Uint<LIMBS>> {
    let maybe_inverse = x.inv_odd_mod(modulus);
    let (inverse, is_some) = maybe_inverse.components_ref();
    ConstCtOption::new(
        montgomery_reduction(&inverse.split_mul(r3), modulus, mod_neg_inv),
        is_some,
    )
}
