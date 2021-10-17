//! Limb bit not operations.

use super::Limb;
use core::ops::Not;

impl Limb {
    /// Calculates `!a`.
    pub const fn bitnot(self) -> Self {
        Limb(!self.0)
    }
}

impl Not for Limb {
    type Output = Limb;

    fn not(self) -> <Self as Not>::Output {
        self.bitnot()
    }
}
