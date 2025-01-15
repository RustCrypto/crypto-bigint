use super::reduction::montgomery_reduction;
use crate::{Limb, Odd, Uint};

#[cfg(all(target_os = "zkvm", target_arch = "riscv32"))]
use crate::powdr;

pub(crate) fn mul_montgomery_form<const LIMBS: usize>(
    a: &Uint<LIMBS>,
    b: &Uint<LIMBS>,
    modulus: &Odd<Uint<LIMBS>>,
    mod_neg_inv: Limb,
) -> Uint<LIMBS> {
    #[cfg(all(target_os = "zkvm", target_arch = "riscv32"))]
    if LIMBS == powdr::BIGINT_WIDTH_WORDS {
        return powdr::modmul_uint_256(a, b, modulus);
    }

    let product = a.split_mul(b);
    montgomery_reduction::<LIMBS>(&product, modulus, mod_neg_inv)
}

pub(crate) fn square_montgomery_form<const LIMBS: usize>(
    a: &Uint<LIMBS>,
    modulus: &Odd<Uint<LIMBS>>,
    mod_neg_inv: Limb,
) -> Uint<LIMBS> {
    #[cfg(all(target_os = "zkvm", target_arch = "riscv32"))]
    if LIMBS == powdr::BIGINT_WIDTH_WORDS {
        return powdr::modmul_uint_256(a, a, modulus);
    }

    let product = a.square_wide();
    montgomery_reduction::<LIMBS>(&product, modulus, mod_neg_inv)
}
