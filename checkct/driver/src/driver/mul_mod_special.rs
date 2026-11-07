use super::private_limb;
use checkct_macros::checkct;
use core::hint::black_box;
use crypto_bigint::{Limb, Uint};

// Keep every operand bit secret and unrestricted, including values at or above p.
#[inline(always)]
fn private_uint<const LIMBS: usize>() -> Uint<LIMBS> {
    let mut limbs = [Limb::ZERO; LIMBS];
    for limb in &mut limbs {
        *limb = private_limb();
    }
    Uint::new(limbs)
}

macro_rules! check_mul_mod_special {
    ($name:ident, $limbs:literal, $c:expr) => {
        #[checkct]
        pub fn $name() {
            let a = private_uint::<$limbs>();
            let b = private_uint::<$limbs>();
            black_box(a.mul_mod_special(&b, $c));
        }
    };
}

// Use exact limb counts so every target exercises both the reciprocal fallback
// and the special reduction, including its tightest bounds at two limbs.
check_mul_mod_special!(one_limb_secret_c, 1, private_limb());
check_mul_mod_special!(two_limbs_secret_c, 2, private_limb());

// Preserve constant c values at the call site to expose compiler specialization:
// wrapping multiplication, a Mersenne modulus, a small c, and the largest c.
check_mul_mod_special!(one_limb_c0, 1, Limb::ZERO);
check_mul_mod_special!(two_limbs_c0, 2, Limb::ZERO);
check_mul_mod_special!(one_limb_c1, 1, Limb::ONE);
#[cfg(not(target_arch = "aarch64"))] // TODO(tarcieri): BINSEC can't decode `MRS` instruction
check_mul_mod_special!(two_limbs_c1, 2, Limb::ONE);
check_mul_mod_special!(one_limb_c19, 1, Limb(19));
check_mul_mod_special!(two_limbs_c19, 2, Limb(19));
check_mul_mod_special!(one_limb_max_c, 1, Limb::MAX);
check_mul_mod_special!(two_limbs_max_c, 2, Limb::MAX);

// Three limbs also permit the first reduction's carry to reach Limb::MAX.
#[cfg(not(target_arch = "aarch64"))] // TODO(tarcieri): BINSEC can't decode `MRS` instruction
check_mul_mod_special!(three_limbs_secret_c, 3, private_limb());
#[cfg(not(target_arch = "aarch64"))] // TODO(tarcieri): BINSEC can't decode `MRS` instruction
check_mul_mod_special!(three_limbs_max_c, 3, Limb::MAX);
