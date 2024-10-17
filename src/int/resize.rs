use crate::Int;

impl<const LIMBS: usize> Int<LIMBS> {
    /// Resize the representation of `self` to an `Int<T>`.
    /// Warning: this operation may lead to loss of information.
    #[inline(always)]
    pub const fn resize<const T: usize>(&self) -> Int<T> {
        Int::new_from_uint(self.0.resize::<T>())
    }
}
