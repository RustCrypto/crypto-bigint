use crate::{Int, Uint};
use crate::uint::new_gcd::extension::ExtendedInt;

type Vector<T> = (T, T);

pub(crate) struct IntMatrix<const LIMBS: usize, const DIM: usize>([[Int<LIMBS>; DIM]; DIM]);

impl<const LIMBS: usize> IntMatrix<LIMBS, 2> {

    pub(crate) const fn new(m00: Int<LIMBS>, m01: Int<LIMBS>, m10: Int<LIMBS>, m11: Int<LIMBS>) -> Self {
        Self([[m00, m10], [m01, m11]])
    }

    /// Apply this matrix to a vector of [Uint]s, returning the result as a vector of
    /// [ExtendedInt]s.
    #[inline]
    pub(crate) const fn extended_apply_to<const VEC_LIMBS: usize>(
        &self,
        vec: Vector<Uint<VEC_LIMBS>>,
    ) -> Vector<ExtendedInt<VEC_LIMBS, LIMBS>> {
        let (a, b) = vec;
        let a00 = ExtendedInt::from_product(a, self.0[0][0]);
        let a01 = ExtendedInt::from_product(a, self.0[0][1]);
        let b10 = ExtendedInt::from_product(b, self.0[1][0]);
        let b11 = ExtendedInt::from_product(b, self.0[1][1]);
        (a00.wrapping_add(&b10), a01.wrapping_add(&b11))
    }
}