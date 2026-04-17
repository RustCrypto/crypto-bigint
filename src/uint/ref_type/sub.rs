use super::UintRef;
use crate::Limb;
use ctutils::Choice;

impl UintRef {
    /// Perform an in-place borrowing sub of a limb, returning the borrowed limb value.
    #[inline]
    pub const fn borrowing_sub_assign_limb(&mut self, mut rhs: Limb, mut borrow: Limb) -> Limb {
        let mut i = 0;
        while i < self.limbs.len() {
            (self.limbs[i], borrow) = self.limbs[i].borrowing_sub(rhs, borrow);
            rhs = Limb::ZERO;
            i += 1;
        }
        borrow
    }

    /// Perform an in-place borrowing subtraction of another [`UintRef`], returning the carried limb
    /// value.
    ///
    /// # Panics
    /// If `self` is shorter than `rhs`.
    #[inline]
    #[track_caller]
    pub const fn borrowing_sub_assign(&mut self, rhs: &Self, borrow: Limb) -> Limb {
        self.borrowing_sub_assign_slice(&rhs.limbs, borrow)
    }

    /// Perform an in-place borrowing subtraction of another limb slice, returning the borrowed limb
    /// value.
    ///
    /// # Panics
    /// If `self` is shorter than `rhs`.
    #[inline]
    #[track_caller]
    pub const fn borrowing_sub_assign_slice(&mut self, rhs: &[Limb], mut borrow: Limb) -> Limb {
        assert!(
            self.limbs.len() >= rhs.len(),
            "length mismatch in borrowing_sub_assign_slice"
        );
        let mut i = 0;
        while i < rhs.len() {
            (self.limbs[i], borrow) = self.limbs[i].borrowing_sub(rhs[i], borrow);
            i += 1;
        }
        while i < self.limbs.len() {
            (self.limbs[i], borrow) = self.limbs[i].borrowing_sub(Limb::ZERO, borrow);
            i += 1;
        }
        borrow
    }

    /// Perform in-place wrapping subtraction, returning the truthy value as the second element of
    /// the tuple if an underflow has occurred.
    ///
    /// # Panics
    /// If `self` is shorter than `rhs`.
    #[track_caller]
    pub(crate) const fn conditional_borrowing_sub_assign(
        &mut self,
        rhs: &Self,
        choice: Choice,
    ) -> Choice {
        assert!(
            self.limbs.len() >= rhs.limbs.len(),
            "length mismatch in conditional_borrowing_sub_assign"
        );
        let mask = Limb::select(Limb::ZERO, Limb::MAX, choice);
        let mut borrow = Limb::ZERO;

        let mut i = 0;
        while i < rhs.limbs.len() {
            let masked_rhs = rhs.limbs[i].bitand(mask);
            (self.limbs[i], borrow) = self.limbs[i].borrowing_sub(masked_rhs, borrow);
            i += 1;
        }
        while i < self.limbs.len() {
            (self.limbs[i], borrow) = self.limbs[i].borrowing_sub(Limb::ZERO, borrow);
            i += 1;
        }

        borrow.lsb_to_choice()
    }
}
