use crate::{ConstantTimeSelect, Int, Uint};

impl<const LIMBS: usize> Int<LIMBS> {
    /// Expand the representation of `self` to an `Int<T>`.
    /// Assumes `T >= LIMBS`; panics otherwise.
    #[inline(always)]
    pub fn expand<const T: usize>(&self) -> Int<T> {
        assert!(T >= LIMBS);
        let mut res = Uint::ct_select(&Int::ZERO.0, &Int::FULL_MASK.0, self.is_negative().into());
        let mut i = 0;
        while i < LIMBS {
            res.limbs[i] = self.0.limbs[i];
            i += 1;
        }
        Int::new_from_uint(res)
    }
}
