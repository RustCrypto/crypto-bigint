//! GCD support for [`Limb`].

use super::Limb;
use crate::{Gcd, NonZero, Odd, Uint};

impl Gcd for Limb {
    type Output = Limb;

    fn gcd(&self, rhs: &Self) -> Self::Output {
        Uint::<1>::from(*self).gcd(&Uint::from(*rhs)).limbs[0]
    }

    fn gcd_vartime(&self, rhs: &Self) -> Self::Output {
        Uint::<1>::from(*self).gcd_vartime(&Uint::from(*rhs)).limbs[0]
    }
}

impl Gcd<Limb> for NonZero<Limb> {
    type Output = Limb;

    fn gcd(&self, rhs: &Limb) -> Self::Output {
        NonZero::<Uint<1>>::from(*self).gcd(&Uint::from(*rhs)).limbs[0]
    }

    fn gcd_vartime(&self, rhs: &Limb) -> Self::Output {
        NonZero::<Uint<1>>::from(*self)
            .gcd_vartime(&Uint::from(*rhs))
            .limbs[0]
    }
}

impl Gcd<Limb> for Odd<Limb> {
    type Output = Limb;

    fn gcd(&self, rhs: &Limb) -> Self::Output {
        Odd::<Uint<1>>::from(*self).gcd(&Uint::from(*rhs)).limbs[0]
    }

    fn gcd_vartime(&self, rhs: &Limb) -> Self::Output {
        Odd::<Uint<1>>::from(*self)
            .gcd_vartime(&Uint::from(*rhs))
            .limbs[0]
    }
}
