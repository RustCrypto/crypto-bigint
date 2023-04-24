use crate::{NonZero, Uint, Wrapping, Zero};
use num_traits::{Num, NumOps};
use core::ops::{Add, Div, Mul, Rem, Sub};
use crate::modular::runtime_mod::DynResidue;

/* Wrapping<Uint<LIMBS>> */
impl<const LIMBS: usize> num_traits::Zero for Wrapping<Uint<LIMBS>> {
    fn zero() -> Self {
        Self::ZERO
    }

    // TODO: if I perform this equality in this manner, do I lose constant-timeness? Can I do it another way?
    fn is_zero(&self) -> bool {
        self == &Self::ZERO
    }
}

impl<const LIMBS: usize> num_traits::One for Wrapping<Uint<LIMBS>> {
    fn one() -> Self {
        Wrapping(Uint::<LIMBS>::ONE)
    }
}

impl<const LIMBS: usize> Div<Wrapping<Uint<LIMBS>>> for Wrapping<Uint<LIMBS>> {
    type Output = Wrapping<Uint<LIMBS>>;

    // TODO: this panics in case of division by zero, is this the intended behavior? (can't see any other option that would comply with the trait)
    fn div(self, rhs: Wrapping<Uint<LIMBS>>) -> Self::Output {
        self / NonZero::new(rhs.0).unwrap()
    }
}

impl<const LIMBS: usize> Rem<Wrapping<Uint<LIMBS>>> for Wrapping<Uint<LIMBS>> {
    type Output = Wrapping<Uint<LIMBS>>;

    // TODO: this panics in case of division by zero, is this the intended behavior? (can't see any other option that would comply with the trait)
    fn rem(self, rhs: Wrapping<Uint<LIMBS>>) -> Self::Output {
        self % NonZero::new(rhs.0).unwrap()
    }
}

impl<const LIMBS: usize> Num for Wrapping<Uint<LIMBS>> {
    type FromStrRadixErr = ();

    // TODO: what's the best way to do this?
    fn from_str_radix(str: &str, radix: u32) -> Result<Self, Self::FromStrRadixErr> {
        todo!()
    }
}

/* DynResidue<LIMBS> */
impl<const LIMBS: usize> num_traits::Zero for DynResidue<LIMBS> {
    // TODO: I don't have access to self here, and thus no access to params().
    // So how can I know the modulo, so to construct a valid zero value for?
    fn zero() -> Self {
        todo!()
    }

    // TODO: if I perform this equality in this manner, do I lose constant-timeness? Can I do it another way?
    fn is_zero(&self) -> bool {
        todo!()
    }
}

impl<const LIMBS: usize> num_traits::One for DynResidue<LIMBS> {
    // TODO: I don't have access to self here, and thus no access to params().
    // So how can I know the modulo, so to construct a valid one value for?
    fn one() -> Self {
        todo!()
    }
}

impl<const LIMBS: usize> Div<DynResidue<LIMBS>> for DynResidue<LIMBS> {
    type Output = DynResidue<LIMBS>;

    // TODO: how to handle the case in which the element is non-invertible?
    fn div(self, rhs: DynResidue<LIMBS>) -> Self::Output {
        self * (rhs.invert().0)
    }
}

impl<const LIMBS: usize> Rem<DynResidue<LIMBS>> for DynResidue<LIMBS> {
    type Output = DynResidue<LIMBS>;

    // TODO: I'm not sure what it means to perform Rem for a ring element..
    fn rem(self, rhs: DynResidue<LIMBS>) -> Self::Output {
        todo!()
    }
}

impl<const LIMBS: usize> Num for DynResidue<LIMBS> {
    type FromStrRadixErr = ();

    // TODO: what's the best way to do this?
    fn from_str_radix(str: &str, radix: u32) -> Result<Self, Self::FromStrRadixErr> {
        todo!()
    }
}
