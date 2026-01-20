//! Parameter calculation for prime moduli.

use core::num::NonZeroU32;
use ctutils::{CtAssignSlice, CtEqSlice, CtSelectUsingCtAssign};

use super::{FixedMontyForm, FixedMontyParams};
use crate::{Choice, CtAssign, CtEq, Odd, Uint};

#[cfg(feature = "subtle")]
use crate::CtSelect;

/// Parameters for supporting efficient computations on integers in Montgomery form
/// with a prime modulus.
#[derive(Debug, Copy, Clone)]
pub struct PrimeParams<const LIMBS: usize> {
    /// A constant such that the modulus `p = t•2^s+1` for `s > 0` and some odd `t`.
    pub(super) s: NonZeroU32,
    /// The smallest primitive root of the modulus.
    pub(super) generator: NonZeroU32,
    /// The exponent to use in computing a modular square root.
    pub(super) sqrt_exp: Uint<LIMBS>,
    /// An s'th root of unity for the modulus, in Montgomery form.
    pub(super) monty_root_unity: Uint<LIMBS>,
    /// Equal to `monty_root_unity^2 mod p`.
    pub(super) monty_root_unity_p2: Uint<LIMBS>,
}

impl<const LIMBS: usize> PrimeParams<LIMBS> {
    /// Instantiates a new set of [`PrimeParams`] given [`FixedMontyParams`] for a prime modulus.
    #[must_use]
    #[allow(clippy::unwrap_in_result, clippy::missing_panics_doc)]
    pub const fn new_vartime(params: &FixedMontyParams<LIMBS>) -> Option<Self> {
        // A primitive root exists if and only if n is 1, 2, 4, p^k or 2p^k, k > 0, p is an odd prime

        let p = params.modulus();
        let p_minus_one = p.as_ref().set_bit_vartime(0, false);
        let s = NonZeroU32::new(p_minus_one.trailing_zeros_vartime()).expect("ensured non-zero");

        let Some((generator, gen_uint)) = find_primitive_root(p) else {
            return None;
        };

        // if s=1 and p is a power of a prime then -1 is always a root of unity
        let (exp, root) = if s.get() == 1 {
            // (p+1)/4
            let exp = p.as_ref().shr_vartime(2).wrapping_add(&Uint::ONE);
            let root = FixedMontyForm::new(&p_minus_one, params);
            (exp, root)
        } else {
            // t = (p-1)/2^s
            let t = p.as_ref().shr_vartime(s.get());
            // exp = (t-1)/2
            let exp = t.shr_vartime(1);
            // the s'th root of unity is calculated as `generator^t`
            let root = FixedMontyForm::new(&gen_uint, params).pow_vartime(&t);
            (exp, root)
        };

        Some(Self {
            s,
            generator,
            sqrt_exp: exp,
            monty_root_unity: root.to_montgomery(),
            monty_root_unity_p2: root.square().to_montgomery(),
        })
    }

    /// Get the constant 'generator' used in modular square root calculation.
    #[must_use]
    pub const fn generator(&self) -> NonZeroU32 {
        self.generator
    }

    /// Get the constant 's' used in modular square root calculation.
    #[must_use]
    pub const fn s(&self) -> NonZeroU32 {
        self.s
    }
}

impl<const LIMBS: usize> CtAssign for PrimeParams<LIMBS> {
    fn ct_assign(&mut self, other: &Self, choice: Choice) {
        self.s.ct_assign(&other.s, choice);
        self.generator.ct_assign(&other.generator, choice);
        self.sqrt_exp.ct_assign(&other.sqrt_exp, choice);
        self.monty_root_unity
            .ct_assign(&other.monty_root_unity, choice);
        self.monty_root_unity_p2
            .ct_assign(&other.monty_root_unity_p2, choice);
    }
}
impl<const LIMBS: usize> CtAssignSlice for PrimeParams<LIMBS> {}
impl<const LIMBS: usize> CtSelectUsingCtAssign for PrimeParams<LIMBS> {}

impl<const LIMBS: usize> CtEq for PrimeParams<LIMBS> {
    fn ct_eq(&self, other: &Self) -> Choice {
        self.s.ct_eq(&other.s)
            & self.generator.ct_eq(&other.generator)
            & self.sqrt_exp.ct_eq(&other.sqrt_exp)
            & self.monty_root_unity.ct_eq(&other.monty_root_unity)
            & self.monty_root_unity_p2.ct_eq(&other.monty_root_unity_p2)
    }
}
impl<const LIMBS: usize> CtEqSlice for PrimeParams<LIMBS> {}

#[cfg(feature = "subtle")]
impl<const LIMBS: usize> subtle::ConstantTimeEq for PrimeParams<LIMBS> {
    fn ct_eq(&self, other: &Self) -> subtle::Choice {
        CtEq::ct_eq(self, other).into()
    }
}

#[cfg(feature = "subtle")]
impl<const LIMBS: usize> subtle::ConditionallySelectable for PrimeParams<LIMBS> {
    fn conditional_assign(&mut self, src: &Self, choice: subtle::Choice) {
        self.ct_assign(src, choice.into());
    }

    fn conditional_select(a: &Self, b: &Self, choice: subtle::Choice) -> Self {
        a.ct_select(b, choice.into())
    }
}

#[allow(clippy::unwrap_in_result)]
const fn find_primitive_root<const LIMBS: usize>(
    p: &Odd<Uint<LIMBS>>,
) -> Option<(NonZeroU32, Uint<LIMBS>)> {
    // Find a quadratic non-residue (primitive roots are non-residue for powers of a prime)
    let mut g = NonZeroU32::new(2u32).expect("ensured non-zero");
    loop {
        // Either the modulus is prime and g is quadratic non-residue, or
        // the modulus is composite.
        let g_uint = Uint::from_u32(g.get());
        match g_uint.jacobi_symbol_vartime(p) as i8 {
            -1 => {
                break Some((g, g_uint));
            }
            0 => {
                // Modulus is composite
                return None;
            }
            _ => {
                let Some(g2) = g.checked_add(1) else {
                    return None;
                };
                g = g2;
            }
        }
    }
}
