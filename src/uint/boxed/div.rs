//! [`BoxedUint`] division operations.

use crate::{BoxedUint, Limb};
use subtle::{ConstantTimeEq, CtOption};

impl BoxedUint {
    /// Computes self % rhs, returns the remainder.
    ///
    /// Variable-time with respect to `rhs`.
    ///
    /// Panics if `self` and `rhs` have different precisions.
    // TODO(tarcieri): make infallible by making `rhs` into `NonZero`; don't panic
    pub fn rem_vartime(&self, rhs: &Self) -> CtOption<Self> {
        debug_assert_eq!(self.nlimbs(), rhs.nlimbs());
        let mb = rhs.bits();
        let mut bd = self.bits_precision() - mb;
        let mut rem = self.clone();
        let mut c = rhs.shl_vartime(bd);

        loop {
            let (r, borrow) = rem.sbb(&c, Limb::ZERO);
            rem = Self::conditional_select(&r, &rem, !borrow.ct_eq(&Limb::ZERO));
            if bd == 0 {
                break;
            }
            bd -= 1;
            c = c.shr_vartime(1);
        }

        CtOption::new(rem, !(mb as u32).ct_eq(&0))
    }
}

#[cfg(test)]
mod tests {
    use super::BoxedUint;

    #[test]
    fn rem_vartime() {
        let n = BoxedUint::from(0xFFEECCBBAA99887766u128);
        let p = BoxedUint::from(997u128);
        assert_eq!(BoxedUint::from(648u128), n.rem_vartime(&p).unwrap());
    }
}
