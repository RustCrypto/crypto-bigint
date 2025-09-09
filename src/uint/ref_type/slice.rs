use super::UintRef;
use crate::Limb;

impl UintRef {
    /// Fill the limb slice with a repeated limb value.
    #[inline(always)]
    pub const fn fill(&mut self, limb: Limb) {
        let mut i = 0;
        while i < self.0.len() {
            self.0[i] = limb;
            i += 1;
        }
    }

    /// Split the mutable limb slice at index `mid`, producing head and tail slices.
    #[cfg(feature = "alloc")]
    #[inline]
    #[track_caller]
    pub const fn split_at_mut(&mut self, mid: usize) -> (&mut Self, &mut Self) {
        let (a, b) = self.0.split_at_mut(mid);
        (UintRef::new_mut(a), UintRef::new_mut(b))
    }

    /// Access a limb slice up to a number of elements `len`.
    #[inline]
    #[track_caller]
    pub const fn leading(&self, len: usize) -> &Self {
        Self::new(self.0.split_at(len).0)
    }

    /// Access a mutable limb slice up to a number of elements `len`.
    #[inline]
    #[track_caller]
    pub const fn leading_mut(&mut self, len: usize) -> &mut Self {
        Self::new_mut(self.0.split_at_mut(len).0)
    }

    /// Access a mutable limb slice starting from the index `start`.
    #[inline]
    #[track_caller]
    pub const fn trailing_mut(&mut self, start: usize) -> &mut Self {
        Self::new_mut(self.0.split_at_mut(start).1)
    }
}
