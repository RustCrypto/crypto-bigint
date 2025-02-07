//! This module implements (a constant variant of) the Optimized Extended Binary GCD algorithm,
//! which is described by Pornin in "Optimized Binary GCD for Modular Inversion".
//! Ref: <https://eprint.iacr.org/2020/972.pdf>

use crate::{Int, Uint};

impl<const LIMBS: usize> Int<LIMBS> {
    /// Executes the Binary Extended GCD algorithm.
    ///
    /// Given `(self, rhs)`, computes `(g, x, y)`, s.t. `self * x + rhs * y = g = gcd(self, rhs)`.
    pub const fn binxgcd(&self, rhs: &Self) -> (Uint<LIMBS>, Self, Self) {
        let (abs_self, sgn_self) = self.abs_sign();
        let (abs_rhs, sgn_rhs) = rhs.abs_sign();
        let (gcd, x, y) = abs_self.binxgcd(&abs_rhs);
        (gcd, x.wrapping_neg_if(sgn_self), y.wrapping_neg_if(sgn_rhs))
    }
}
