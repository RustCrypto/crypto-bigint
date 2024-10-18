//! `From`-like conversions for [`Int`].

#[cfg(target_pointer_width = "32")]
use crate::ConstChoice;
use crate::{Int, Limb, Uint, Word, I128, I64};

impl<const LIMBS: usize> Int<LIMBS> {
    /// Create a [`Int`] from an `i8` (const-friendly)
    // TODO(tarcieri): replace with `const impl From<i8>` when stable
    pub const fn from_i8(n: i8) -> Self {
        assert!(LIMBS >= 1, "number of limbs must be greater than zero");
        Int::new_from_uint(Uint::new([Limb(n as Word)])).resize()
    }

    /// Create a [`Int`] from an `i16` (const-friendly)
    // TODO(tarcieri): replace with `const impl From<i16>` when stable
    pub const fn from_i16(n: i16) -> Self {
        assert!(LIMBS >= 1, "number of limbs must be greater than zero");
        Int::new_from_uint(Uint::new([Limb(n as Word)])).resize()
    }

    /// Create a [`Int`] from an `i32` (const-friendly)
    // TODO(tarcieri): replace with `const impl From<i32>` when stable
    pub fn from_i32(n: i32) -> Self {
        assert!(LIMBS >= 1, "number of limbs must be greater than zero");
        Int::new_from_uint(Uint::new([Limb(n as Word)])).resize()
    }

    /// Create a [`Int`] from an `i64` (const-friendly)
    // TODO(tarcieri): replace with `const impl From<i64>` when stable
    #[cfg(target_pointer_width = "32")]
    pub const fn from_i64(n: i64) -> Self {
        assert!(LIMBS >= 2, "number of limbs must be two or greater");
        let hi = (n >> 32) as u32;
        let is_negative = ConstChoice::from_word_msb(hi);
        let limb = Limb::select(Limb::ZERO, Limb::MAX, is_negative);
        let mut limbs = [limb; LIMBS];
        limbs[0].0 = (n & 0xFFFFFFFF) as u32;
        limbs[0].0 = hi;
        Self(Uint::new(limbs))
    }

    /// Create a [`Int`] from an `i64` (const-friendly)
    // TODO(tarcieri): replace with `const impl From<i64>` when stable
    #[cfg(target_pointer_width = "64")]
    pub const fn from_i64(n: i64) -> Self {
        assert!(LIMBS >= 1, "number of limbs must be greater than zero");
        Int::new_from_uint(Uint::new([Limb(n as Word)])).resize()
    }

    /// Create a [`Int`] from an `i128` (const-friendly)
    // TODO(tarcieri): replace with `const impl From<i128>` when stable
    pub const fn from_i128(n: i128) -> Self {
        Int::new_from_uint(Uint::<{ I128::LIMBS }>::from_u128(n as u128)).resize()
    }
}

impl<const LIMBS: usize> From<i8> for Int<LIMBS> {
    fn from(n: i8) -> Self {
        // TODO(tarcieri): const where clause when possible
        debug_assert!(LIMBS > 0, "limbs must be non-zero");
        Self::from_i8(n)
    }
}

impl<const LIMBS: usize> From<i16> for Int<LIMBS> {
    fn from(n: i16) -> Self {
        // TODO(tarcieri): const where clause when possible
        debug_assert!(LIMBS > 0, "limbs must be non-zero");
        Self::from_i16(n)
    }
}

impl<const LIMBS: usize> From<i32> for Int<LIMBS> {
    fn from(n: i32) -> Self {
        // TODO(tarcieri): const where clause when possible
        debug_assert!(LIMBS > 0, "limbs must be non-zero");
        Self::from_i32(n)
    }
}

impl<const LIMBS: usize> From<i64> for Int<LIMBS> {
    fn from(n: i64) -> Self {
        // TODO(tarcieri): const where clause when possible
        debug_assert!(LIMBS >= 8 / Limb::BYTES, "not enough limbs");
        Self::from_i64(n)
    }
}

impl<const LIMBS: usize> From<i128> for Int<LIMBS> {
    fn from(n: i128) -> Self {
        // TODO(tarcieri): const where clause when possible
        debug_assert!(LIMBS >= 16 / Limb::BYTES, "not enough limbs");
        Self::from_i128(n)
    }
}

impl From<I64> for i64 {
    fn from(n: I64) -> i64 {
        u64::from(n.0) as i64
    }
}

impl From<I128> for i128 {
    fn from(n: I128) -> i128 {
        u128::from(n.0) as i128
    }
}

impl<const LIMBS: usize, const LIMBS2: usize> From<&Int<LIMBS>> for Int<LIMBS2> {
    fn from(num: &Int<LIMBS>) -> Int<LIMBS2> {
        num.resize()
    }
}

#[cfg(test)]
mod tests {
    #[cfg(target_pointer_width = "64")]
    use crate::I128 as IntEx;
    #[cfg(target_pointer_width = "32")]
    use crate::I64 as IntEx;
    use crate::{Limb, I128};

    #[test]
    fn from_i8() {
        let n = IntEx::from(42i8);
        assert_eq!(n.as_limbs(), &[Limb(42), Limb(0)]);
        let n = IntEx::from(-42i8);
        assert_eq!(n.as_limbs(), &[Limb::MAX - Limb::from(41u32), Limb::MAX]);
    }

    #[test]
    fn from_i16() {
        let n = IntEx::from(42i16);
        assert_eq!(n.as_limbs(), &[Limb(42), Limb(0)]);
        let n = IntEx::from(-42i16);
        assert_eq!(n.as_limbs(), &[Limb::MAX - Limb::from(41u32), Limb::MAX]);
    }

    #[test]
    fn from_i32() {
        let n = IntEx::from(42i32);
        assert_eq!(n.as_limbs(), &[Limb(42), Limb(0)]);
        let n = IntEx::from(-42i32);
        assert_eq!(n.as_limbs(), &[Limb::MAX - Limb::from(41u32), Limb::MAX]);
    }

    #[test]
    fn from_i64() {
        let n = IntEx::from(42i64);
        assert_eq!(n.as_limbs(), &[Limb(42), Limb(0)]);
        let n = IntEx::from(-42i64);
        assert_eq!(n.as_limbs(), &[Limb::MAX - Limb::from(41u32), Limb::MAX]);
    }

    #[test]
    fn from_i128() {
        let n = I128::from(42i128);
        assert_eq!(&n.as_limbs()[..2], &[Limb(42), Limb(0)]);
        assert_eq!(i128::from(n), 42i128);
        let n = I128::from(-42i128);
        assert_eq!(&n.as_limbs()[..2], &[Limb::MAX - Limb(41), Limb::MAX]);
        assert_eq!(i128::from(n), -42i128);
    }
}
