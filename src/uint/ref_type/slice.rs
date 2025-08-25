use super::UintRef;
use crate::Limb;

impl UintRef {
    /// Copy the contents from a [`UintRef`].
    #[inline(always)]
    pub const fn copy_from(&mut self, rhs: &UintRef) {
        self.copy_from_slice(&rhs.0);
    }

    /// Copy the contents from a limb slice.
    #[inline(always)]
    pub const fn copy_from_slice(&mut self, limbs: &[Limb]) {
        // TODO core::slice::copy_from_slice should eventually be const
        debug_assert!(self.0.len() == limbs.len(), "length mismatch");
        let mut i = 0;
        while i < self.0.len() {
            self.0[i] = limbs[i];
            i += 1;
        }
    }

    /// Fill the limb slice with a repeated limb value.
    #[inline(always)]
    pub const fn fill(&mut self, limb: Limb) {
        let mut i = 0;
        while i < self.0.len() {
            self.0[i] = limb;
            i += 1;
        }
    }

    /// Split the mutable limb slice at a fixed position, producing head and tail slices.
    #[cfg(feature = "alloc")]
    #[inline]
    pub const fn split_at_mut(&mut self, mid: usize) -> (&mut Self, &mut Self) {
        let (a, b) = self.0.split_at_mut(mid);
        (UintRef::new_mut(a), UintRef::new_mut(b))
    }

    /// Access a limb slice up to a fixed position.
    #[inline]
    pub const fn leading(&self, len: usize) -> &Self {
        Self::new(self.0.split_at(len).0)
    }

    /// Access a mutable limb slice up to a fixed position.
    #[inline]
    pub const fn leading_mut(&mut self, len: usize) -> &mut Self {
        Self::new_mut(self.0.split_at_mut(len).0)
    }

    /// Access a mutable limb slice starting from a fixed position.
    #[inline]
    pub const fn trailing_mut(&mut self, start: usize) -> &mut Self {
        Self::new_mut(self.0.split_at_mut(start).1)
    }
}
