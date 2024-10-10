//! Stack-allocated big signed integers.

use num_traits::Zero;
use subtle::{Choice, ConditionallySelectable, ConstantTimeEq};

use crate::{Limb, Uint};

mod add;
mod cmp;
mod neg;
mod sub;

#[derive(Copy, Clone, Hash, Debug, PartialEq)]
pub struct Int<const LIMBS: usize> {
    // TODO(erik): replace with Choice once I've figured how to const-construct those.
    is_negative: bool,
    magnitude: Uint<LIMBS>,
}

impl<const LIMBS: usize> Int<LIMBS> {
    /// The value `0`.
    pub const ZERO: Self = Self {
        is_negative: false,
        magnitude: Uint::ZERO,
    };

    /// The value `1`.
    pub const ONE: Self = Self {
        is_negative: false,
        magnitude: Uint::ONE,
    };

    /// The value `-1`.
    pub const MINUS_ONE: Self = Self {
        is_negative: true,
        magnitude: Uint::ONE,
    };

    /// Maximum value this [`Uint`] can express.
    pub const MAX: Self = Self {
        is_negative: false,
        magnitude: Uint::MAX,
    };

    /// Smallest value this [`Uint`] can express.
    // Note: keep in mind that when `LIMBS = 0`, the minimal value we can express is zero.
    pub const MIN: Self = Self {
        is_negative: LIMBS != 0,
        magnitude: Uint::MAX,
    };

    /// The number of limbs used on this platform.
    pub const LIMBS: usize = LIMBS;

    /// Const-friendly [`Int`] constructor.
    pub const fn new(is_negative: bool, limbs: [Limb; LIMBS]) -> Self {
        Self {
            is_negative,
            magnitude: Uint::new(limbs),
        }
    }

    /// Const-friendly [`Int`] constructor, using a `Uint`.
    pub const fn new_from_uint(is_negative: bool, magnitude: Uint<LIMBS>) -> Self {
        Self {
            is_negative,
            magnitude,
        }
    }

    /// Whether this [`Int`] is negative
    pub fn is_negative(&self) -> Choice {
        Choice::from(u8::from(self.is_negative))
    }

    /// Whether this [`Int`] is zero
    pub fn is_zero(&self) -> bool {
        self.magnitude.is_zero()
    }
}

impl<const LIMBS: usize> ConditionallySelectable for Int<LIMBS> {
    fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
        let magnitude = Uint::conditional_select(&a.magnitude, &b.magnitude, choice);
        let is_negative = Choice::conditional_select(&a.is_negative(), &b.is_negative(), choice);

        Self {
            is_negative: is_negative.unwrap_u8() == 1,
            magnitude,
        }
    }
}

impl<const LIMBS: usize> Default for Int<LIMBS> {
    fn default() -> Self {
        Self::ZERO
    }
}

impl<const LIMBS: usize> Zero for Int<LIMBS> {
    fn zero() -> Self {
        Self::ZERO
    }

    fn is_zero(&self) -> bool {
        self.ct_eq(&Self::ZERO).into()
    }
}

#[cfg(target_pointer_width = "64")]
type I128 = Int<2>;

#[cfg(target_pointer_width = "32")]
type I128 = Int<4>;

#[cfg(test)]
#[allow(clippy::unwrap_used)]
mod tests {
    use crate::{U128, Uint, int::{I128, Int}};

    #[test]
    fn zero() {
        let n = I128::ZERO;
        assert!(!n.is_negative);
        assert_eq!(n.magnitude, U128::ZERO);
    }

    #[test]
    fn one() {
        let n = I128::ONE;
        assert!(!n.is_negative);
        assert_eq!(n.magnitude, U128::ONE);
    }

    #[test]
    fn minus_one() {
        let n = I128::MINUS_ONE;
        assert!(n.is_negative);
        assert_eq!(n.magnitude, U128::ONE);
    }

    #[test]
    fn min() {
        let n = I128::MIN;
        assert!(n.is_negative);
        assert_eq!(n.magnitude, U128::MAX);

        // Deal with case that LIMBS = 0
        let n = Int::<0>::MIN;
        assert!(!n.is_negative);
        assert_eq!(n.magnitude, Uint::<0>::MAX); // dirty trick; MAX is zero, while ZERO panics.
    }

    #[test]
    fn max() {
        let n = I128::MAX;
        assert!(!n.is_negative);
        assert_eq!(n.magnitude, U128::MAX);
    }
}
