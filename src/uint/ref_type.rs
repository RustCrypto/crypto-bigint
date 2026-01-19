//! Unsigned integer reference type.

mod add;
mod bits;
mod cmp;
mod ct;
mod div;
mod invert_mod;
mod shl;
mod shr;
mod slice;
mod sub;

use crate::{Choice, CtOption, Limb, NonZero, Uint, Word};
use core::{
    fmt,
    ops::{Index, IndexMut},
    ptr,
};

#[cfg(all(doc, feature = "alloc"))]
use crate::BoxedUint;

/// Unsigned integer reference type.
///
/// This type contains a limb slice which can be borrowed from either a [`Uint`] or [`BoxedUint`] and
/// thus provides an abstraction for writing shared implementations.
#[repr(transparent)]
#[derive(PartialEq, Eq)]
pub struct UintRef(pub(crate) [Limb]);

impl UintRef {
    /// Create a [`UintRef`] reference type from a [`Limb`] slice.
    #[inline]
    #[must_use]
    pub const fn new(limbs: &[Limb]) -> &Self {
        // SAFETY: `UintRef` is a `repr(transparent)` newtype for `[Limb]`.
        #[allow(unsafe_code)]
        unsafe {
            &*(ptr::from_ref(limbs) as *const UintRef)
        }
    }

    /// Create a mutable [`UintRef`] reference type from a [`Limb`] slice.
    #[inline]
    pub const fn new_mut(limbs: &mut [Limb]) -> &mut Self {
        // SAFETY: `UintRef` is a `repr(transparent)` newtype for `[Limb]`.
        #[allow(unsafe_code)]
        unsafe {
            &mut *(ptr::from_mut(limbs) as *mut UintRef)
        }
    }

    /// Create a new mutable [`UintRef`] reference type from a slice of [`Limb`] arrays.
    pub const fn new_flattened_mut<const N: usize>(slice: &mut [[Limb; N]]) -> &mut Self {
        // This is a temporary shim for `[[T;N]]::as_flattened_mut` which is only const-stable as of
        // Rust 1.87.
        let len = slice.len() * N;

        // SAFETY: we are converting a slice of limb arrays to a slice of limbs, and `len` has been
        // calculated to be the total number of limbs. The pointer has the lifetime of `slice` and
        // is for `Word`, so we're requesting a slice of words the size of the total number of words
        // in the original slice, and giving it a valid pointer to the first word.
        #[allow(unsafe_code)]
        let slice = unsafe { core::slice::from_raw_parts_mut(slice.as_mut_ptr().cast(), len) };
        Self::new_mut(slice)
    }

    /// Borrow the inner `&[Limb]` slice.
    #[inline]
    #[must_use]
    pub const fn as_slice(&self) -> &[Limb] {
        &self.0
    }

    /// Mutably borrow the inner `&mut [Limb]` slice.
    #[inline]
    pub const fn as_mut_slice(&mut self) -> &mut [Limb] {
        &mut self.0
    }

    /// Borrow the inner limbs as a slice of [`Word`]s.
    #[inline]
    #[must_use]
    pub const fn as_words(&self) -> &[Word] {
        Limb::slice_as_words(&self.0)
    }

    /// Borrow the inner limbs as a mutable slice of [`Word`]s.
    #[inline]
    pub const fn as_mut_words(&mut self) -> &mut [Word] {
        Limb::slice_as_mut_words(&mut self.0)
    }

    /// Get an iterator over the inner limbs.
    #[inline]
    #[must_use]
    pub fn iter(&self) -> impl DoubleEndedIterator<Item = &Limb> {
        self.0.iter()
    }

    /// Get a mutable iterator over the inner limbs.
    #[inline]
    #[allow(dead_code)] // TODO(tarcieri): use this
    pub fn iter_mut(&mut self) -> impl DoubleEndedIterator<Item = &mut Limb> {
        self.0.iter_mut()
    }

    /// Access the number of limbs.
    #[inline]
    #[must_use]
    pub const fn nlimbs(&self) -> usize {
        self.0.len()
    }

    /// Conditionally assign all of the limbs to zero.
    #[inline(always)]
    pub const fn conditional_set_zero(&mut self, choice: Choice) {
        let mut i = 0;
        while i < self.nlimbs() {
            self.0[i] = Limb::select(self.0[i], Limb::ZERO, choice);
            i += 1;
        }
    }

    /// Conditionally assign all of the limbs to the maximum.
    #[cfg(feature = "alloc")]
    #[inline]
    pub const fn conditional_set_max(&mut self, choice: Choice) {
        let mut i = 0;
        while i < self.nlimbs() {
            self.0[i] = Limb::select(self.0[i], Limb::MAX, choice);
            i += 1;
        }
    }

    /// Extract up to `LIMBS` limbs into a new `Uint`.
    #[must_use]
    pub const fn to_uint_resize<const LIMBS: usize>(&self) -> Uint<LIMBS> {
        let mut out = Uint::ZERO;
        let len = if self.nlimbs() > LIMBS {
            LIMBS
        } else {
            self.nlimbs()
        };
        let mut i = 0;
        while i < len {
            out.limbs[i] = self.0[i];
            i += 1;
        }
        out
    }

    /// Conditionally construct a [`NonZero`] from this reference.
    ///
    /// To ensure constant-time operation, we need a placeholder value which is used in the event
    /// we return the [`CtOption`] equivalent of `None` which is identical in length to `self`.
    /// And since we're working with reference types, there's only one place to get that: `self`.
    ///
    /// So, this function requires a mutable reference so in the event the provided value is zero
    /// it can change it to be non-zero.
    ///
    /// # Panics
    /// If `self.nlimbs()` is zero.
    #[inline]
    #[must_use]
    pub const fn to_nz(&mut self) -> CtOption<NonZero<&mut Self>> {
        assert!(!self.0.is_empty(), "cannot be used with empty slices");
        let is_nz = self.is_nonzero();

        // If `self` is zero, set the first limb to `1` to make it non-zero.
        self.0[0] = Limb::select(Limb::ONE, self.0[0], is_nz);
        CtOption::new(NonZero(self), is_nz)
    }

    /// Construct a [`NonZero`] reference, returning [`None`] in the event `self` is `0`.
    #[inline]
    #[must_use]
    pub const fn to_nz_vartime(&self) -> Option<NonZero<&Self>> {
        if !self.is_empty() && self.is_nonzero().to_bool_vartime() {
            Some(NonZero(self))
        } else {
            None
        }
    }

    /// Construct a mutable [`NonZero`] reference, returning [`None`] in the event `self` is `0`.
    #[must_use]
    pub const fn to_mut_nz_vartime(&mut self) -> Option<NonZero<&mut Self>> {
        if !self.is_empty() && self.is_nonzero().to_bool_vartime() {
            Some(NonZero(self))
        } else {
            None
        }
    }

    /// Get the least significant 64-bits.
    #[inline(always)]
    pub(crate) const fn lowest_u64(&self) -> u64 {
        #[cfg(target_pointer_width = "32")]
        {
            debug_assert!(self.nlimbs() >= 1);
            let mut ret = self.0[0].0 as u64;

            if self.nlimbs() >= 2 {
                ret |= (self.0[1].0 as u64) << 32;
            }

            ret
        }

        #[cfg(target_pointer_width = "64")]
        {
            self.0[0].0
        }
    }
}

impl AsRef<[Limb]> for UintRef {
    #[inline]
    fn as_ref(&self) -> &[Limb] {
        self.as_slice()
    }
}

impl AsMut<[Limb]> for UintRef {
    #[inline]
    fn as_mut(&mut self) -> &mut [Limb] {
        self.as_mut_slice()
    }
}

impl Index<usize> for UintRef {
    type Output = Limb;

    #[inline]
    fn index(&self, index: usize) -> &Limb {
        self.0.index(index)
    }
}

impl IndexMut<usize> for UintRef {
    #[inline]
    fn index_mut(&mut self, index: usize) -> &mut Limb {
        self.0.index_mut(index)
    }
}

impl fmt::Debug for UintRef {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "UintRef(0x{self:X})")
    }
}

impl fmt::Binary for UintRef {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if f.alternate() {
            write!(f, "0b")?;
        }

        for limb in self.iter().rev() {
            write!(f, "{:0width$b}", &limb.0, width = Limb::BITS as usize)?;
        }
        Ok(())
    }
}

impl fmt::Display for UintRef {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::UpperHex::fmt(self, f)
    }
}

impl fmt::LowerHex for UintRef {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if f.alternate() {
            write!(f, "0x")?;
        }
        for limb in self.iter().rev() {
            write!(f, "{:0width$x}", &limb.0, width = Limb::BYTES * 2)?;
        }
        Ok(())
    }
}

impl fmt::UpperHex for UintRef {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if f.alternate() {
            write!(f, "0x")?;
        }
        for limb in self.iter().rev() {
            write!(f, "{:0width$X}", &limb.0, width = Limb::BYTES * 2)?;
        }
        Ok(())
    }
}
