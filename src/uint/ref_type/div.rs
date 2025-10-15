//! In-place integer division
//!
//! Based on Section 4.3.1, of The Art of Computer Programming, Volume 2, by Donald E. Knuth.
//! Further explanation at <https://janmr.com/blog/2014/04/basic-multiple-precision-long-division/>

use super::UintRef;
use crate::const_choice::u32_min;
use crate::div_limb::{Reciprocal, div2by1, div3by2};
use crate::{ConstChoice, Limb, NonZero};

impl UintRef {
    /// Computes `self` / `rhs`, returning the quotient in `self` and the remainder in `rhs`.
    ///
    /// This function will panic if the divisor is zero.
    #[inline(always)]
    pub const fn div_rem(&mut self, rhs: &mut Self) {
        let (x, y) = (self, rhs);

        // Short circuit for single-word divisor
        if y.nlimbs() == 1 {
            y.0[0] = x.div_rem_limb(y.0[0].to_nz().expect("zero divisor"));
            return;
        }

        // Compute the size of the divisor
        let ybits = y.bits();
        assert!(ybits > 0, "zero divisor");
        let ywords = ybits.div_ceil(Limb::BITS);

        // Shift the entire divisor such that the high bit is set
        let yz = y.bits_precision() - ybits;
        y.wrapping_shl_assign(yz);

        // Shift the dividend to align the words
        let lshift = yz % Limb::BITS;
        let x_hi = x.shl_assign_limb(lshift);

        Self::div_rem_shifted(x, x_hi, y, ywords);

        x.wrapping_shr_assign_by_limbs(ywords - 1);
        y.shr_assign_limb(lshift);
    }

    /// Computes `self` / `rhs`, returning the quotient in `self` and the remainder in `rhs`.
    ///
    /// This function operates in variable-time with respect to `rhs`. For a fixed divisor,
    /// it operates in constant-time. It will panic if the divisor is zero.
    pub const fn div_rem_vartime(&mut self, rhs: &mut Self) {
        let (x, y) = (self, rhs);
        let xsize = x.nlimbs();
        let ywords = y.bits_vartime().div_ceil(Limb::BITS) as usize;

        match (xsize, ywords) {
            (_, 0) => panic!("zero divisor"),
            (0, _) => {
                // If the quotient is empty, set the remainder to zero and return.
                y.fill(Limb::ZERO);
                return;
            }
            (_, 1) => {
                // Perform limb division
                let rem_limb = x.div_rem_limb(y.0[0].to_nz().expect("zero divisor"));
                y.fill(Limb::ZERO);
                y.0[0] = rem_limb;
                return;
            }
            _ if ywords > xsize => {
                // Divisor is greater than dividend. Return zero and the dividend as the
                // quotient and remainder
                y.leading_mut(xsize).copy_from(x.leading(xsize));
                y.trailing_mut(xsize).fill(Limb::ZERO);
                x.fill(Limb::ZERO);
                return;
            }
            _ => (),
        }

        x.div_rem_large_vartime(y.leading_mut(ywords));

        // Shift the quotient to the low limbs within dividend
        x.wrapping_shr_assign_by_limbs_vartime((ywords - 1) as u32);
    }

    /// Computes `x_lower_upper` % `rhs`, returning the remainder in `rhs`.
    ///
    /// This function will panic if the divisor is zero.
    ///
    /// The `x_lower_upper` tuple represents a wide integer. The size of `x_lower_upper.1` must be
    /// at least as large as `rhs`. `x_lower_upper` is left in an indeterminate state.
    #[inline(always)]
    pub const fn rem_wide(x_lower_upper: (&mut Self, &mut Self), rhs: &mut Self) {
        let (x_lo, x) = x_lower_upper;
        let y = rhs;

        // Short circuit for single-word divisor
        if y.nlimbs() == 1 {
            let reciprocal = Reciprocal::new(y.0[0].to_nz().expect("zero divisor"));
            let carry = x.rem_limb_with_reciprocal(&reciprocal, Limb::ZERO);
            y.0[0] = x_lo.rem_limb_with_reciprocal(&reciprocal, carry);
            return;
        }

        // Compute the size of the divisor
        let ybits = y.bits();
        assert!(ybits > 0, "zero divisor");
        let ywords = ybits.div_ceil(Limb::BITS);

        // Shift the entire divisor such that the high bit is set
        let yz = y.bits_precision() - ybits;
        y.wrapping_shl_assign(yz);

        // Shift the dividend to align the words
        let lshift = yz % Limb::BITS;
        let x_lo_carry = x_lo.shl_assign_limb(lshift);
        let x_hi = x.shl_assign_limb(lshift);
        x.0[0] = x.0[0].bitor(x_lo_carry);

        // Perform the core division algorithm
        Self::rem_wide_shifted((x_lo, x), x_hi, y, ywords);

        // Unshift the remainder from the earlier adjustment
        y.shr_assign_limb(lshift);
    }

    /// Computes `x_lower_upper` % `rhs`, returning the remainder in `rhs`.
    ///
    /// This function operates in variable-time with respect to `rhs`. For a fixed divisor,
    /// it operates in constant-time. It will panic if the divisor is zero.
    ///
    /// The `x_lower_upper` tuple represents a wide integer. The size of `x_lower_upper.1`
    /// must be at least as large as `rhs`. `x_lower_upper` is left in an indeterminate state.
    #[inline(always)]
    pub const fn rem_wide_vartime(x_lower_upper: (&mut Self, &mut Self), rhs: &mut Self) {
        let (x_lo, x) = x_lower_upper;
        let xsize = x.nlimbs();
        let ysize = rhs.bits_vartime().div_ceil(Limb::BITS) as usize;
        let y = rhs.leading_mut(ysize);

        match (xsize, ysize) {
            (_, 0) => panic!("zero divisor"),
            (0, _) => {
                // If the quotient is empty, set the remainder to zero and return.
                y.fill(Limb::ZERO);
                return;
            }
            (_, 1) => {
                // Short circuit for single-word divisor
                let reciprocal = Reciprocal::new(y.0[0].to_nz().expect("zero divisor"));
                y.fill(Limb::ZERO);
                let carry = x.rem_limb_with_reciprocal(&reciprocal, Limb::ZERO);
                y.0[0] = x_lo.rem_limb_with_reciprocal(&reciprocal, carry);
                return;
            }
            _ if ysize > xsize => {
                panic!("divisor too large");
            }
            _ => (),
        }

        let lshift = y.0[ysize - 1].leading_zeros();

        // Shift divisor such that it has no leading zeros
        // This means that div2by1 requires no extra shifts, and ensures that the high word >= b/2
        y.shl_assign_limb_vartime(lshift);

        // Shift the dividend to align the words
        let x_lo_carry = x_lo.shl_assign_limb_vartime(lshift);
        let mut x_hi = x.shl_assign_limb_vartime(lshift);
        x.0[0] = x.0[0].bitor(x_lo_carry);

        // Calculate a reciprocal from the highest word of the divisor
        let reciprocal = Reciprocal::new(y.0[ysize - 1].to_nz().expect("zero divisor"));

        // Perform the core division algorithm
        x_hi = Self::rem_wide_large_shifted(
            (x_lo, x),
            x_hi,
            y,
            ysize as u32,
            reciprocal,
            ConstChoice::TRUE,
        );

        // Copy the remainder to the divisor
        y.leading_mut(ysize - 1).copy_from(x.leading(ysize - 1));
        y.0[ysize - 1] = x_hi;

        // Unshift the remainder from the earlier adjustment
        y.shr_assign_limb_vartime(lshift);
    }

    /// Perform in-place division (`self` / `y`) for a pre-shifted dividend and divisor.
    ///
    /// The dividend and divisor must be left-shifted such that the high bit of the divisor
    /// is set, and `x_hi` holds the top bits of the dividend.
    ///
    /// The quotient is returned in `self` and the remainder in `y`, but these values require
    /// additional correction. This is left to the caller for performance reasons.
    #[inline(always)]
    pub const fn div_rem_shifted(&mut self, mut x_hi: Limb, y: &mut Self, ywords: u32) {
        let x = self;

        // Calculate a reciprocal from the highest word of the divisor
        let reciprocal = Reciprocal::new(y.0[y.nlimbs() - 1].to_nz().expect("zero divisor"));
        debug_assert!(reciprocal.shift() == 0);

        // Perform the core division algorithm
        x_hi = Self::div_rem_large_shifted(x, x_hi, y, ywords, reciprocal, ConstChoice::FALSE);

        // Calculate quotient and remainder for the case where the divisor is a single word.
        let limb_div = ConstChoice::from_u32_eq(1, ywords);
        // Note that `div2by1()` will panic if `x_hi >= reciprocal.divisor_normalized`,
        // but this can only be the case if `limb_div` is falsy, in which case we discard
        // the result anyway, so we conditionally set `x_hi` to zero for this branch.
        let x_hi_adjusted = Limb::select(Limb::ZERO, x_hi, limb_div);
        let (quo2, rem2) = div2by1(x_hi_adjusted.0, x.0[0].0, &reciprocal);

        // Adjust the quotient for single limb division
        x.0[0] = Limb::select(x.0[0], Limb(quo2), limb_div);
        // Copy out the low limb of the remainder
        y.0[0] = Limb::select(x.0[0], Limb(rem2), limb_div);

        // Adjust the remainder, copying `x_hi` to the appropriate position and clearing
        // any extra limbs.
        // Note: branching only based on the size of the operands, which is not secret.
        let min = if x.nlimbs() < y.nlimbs() {
            x.nlimbs()
        } else {
            y.nlimbs()
        };
        let hi_pos = u32_min(x.nlimbs() as u32, ywords - 1);
        let mut i = 1;
        while i < min {
            y.0[i] = Limb::select(
                Limb::ZERO,
                x.0[i],
                ConstChoice::from_u32_lt(i as u32, ywords),
            );
            y.0[i] = Limb::select(y.0[i], x_hi, ConstChoice::from_u32_eq(i as u32, hi_pos));
            i += 1;
        }
        while i < y.nlimbs() {
            y.0[i] = Limb::select(Limb::ZERO, x_hi, ConstChoice::from_u32_eq(i as u32, hi_pos));
            i += 1;
        }
    }

    /// Computes `self` / `y` for a 'large' divisor (>1 limbs), returning the quotient and
    /// the remainder in `self`.
    ///
    /// While the divisor may only be a single limb, additional corrections to the result are
    /// required in this case.
    ///
    /// The dividend and divisor must be left-shifted such that the high bit of the divisor
    /// is set, and `x_hi` holds the top bits of the dividend.
    #[inline(always)]
    pub const fn div_rem_large_shifted(
        &mut self,
        mut x_hi: Limb,
        y: &Self,
        ywords: u32,
        reciprocal: Reciprocal,
        vartime: ConstChoice,
    ) -> Limb {
        let x = self;
        let xsize = x.nlimbs();
        let ysize = y.nlimbs();

        let mut xi = xsize - 1;
        let mut x_xi = x.0[xi];
        let mut i;
        let mut carry;

        while xi > 0 {
            // Divide high dividend words by the high divisor word to estimate the quotient word
            let mut quo = div3by2(x_hi.0, x_xi.0, x.0[xi - 1].0, &reciprocal, y.0[ysize - 2].0);

            // This loop is a no-op once xi is smaller than the number of words in the divisor
            let done = ConstChoice::from_u32_lt(xi as u32, ywords - 1);
            if vartime.and(done).is_true_vartime() {
                break;
            }
            quo = done.select_word(quo, 0);

            // Subtract q*divisor from the dividend
            let borrow = {
                carry = Limb::ZERO;
                let mut borrow = Limb::ZERO;
                let mut tmp;
                i = (xi + 1).saturating_sub(ysize);
                while i <= xi {
                    (tmp, carry) =
                        y.0[ysize + i - xi - 1].carrying_mul_add(Limb(quo), carry, Limb::ZERO);
                    (x.0[i], borrow) = x.0[i].borrowing_sub(tmp, borrow);
                    i += 1;
                }
                (_, borrow) = x_hi.borrowing_sub(carry, borrow);
                borrow
            };

            // If the subtraction borrowed, then decrement quo and add back the divisor
            // The probability of this being needed is very low, about 2/(Limb::MAX+1)
            quo = {
                let ct_borrow = ConstChoice::from_word_mask(borrow.0);
                carry = Limb::ZERO;
                i = (xi + 1).saturating_sub(ysize);
                while i <= xi {
                    (x.0[i], carry) = x.0[i].carrying_add(
                        Limb::select(Limb::ZERO, y.0[ysize + i - xi - 1], ct_borrow),
                        carry,
                    );
                    i += 1;
                }
                ct_borrow.select_word(quo, quo.saturating_sub(1))
            };

            // Store the quotient within dividend and set x_hi to the current highest word
            x_hi = Limb::select(x.0[xi], x_hi, done);
            x.0[xi] = Limb::select(Limb(quo), x.0[xi], done);
            x_xi = Limb::select(x.0[xi - 1], x_xi, done);
            xi -= 1;
        }

        x_hi
    }

    /// Perform in-place variable-time division for a 'large' divisor (>1 limbs). The
    /// quotient is returned in `self` and the remainder in `rhs`.
    #[inline(always)]
    const fn div_rem_large_vartime(&mut self, rhs: &mut Self) {
        let (x, y) = (self, rhs);
        let ysize = y.nlimbs();
        debug_assert!(ysize > 1);
        let lshift = y.0[ysize - 1].leading_zeros();

        // Shift divisor such that it has no leading zeros
        // This means that div2by1 requires no extra shifts, and ensures that the high word >= b/2
        y.shl_assign_limb_vartime(lshift);

        // Shift the dividend to match
        let mut x_hi = x.shl_assign_limb_vartime(lshift);

        // Calculate a reciprocal from the highest word of the divisor
        let reciprocal = Reciprocal::new(y.0[ysize - 1].to_nz().expect("zero divisor"));

        // Perform the core division algorithm
        x_hi = Self::div_rem_large_shifted(x, x_hi, y, ysize as u32, reciprocal, ConstChoice::TRUE);

        // Copy the remainder to divisor
        y.leading_mut(ysize - 1).copy_from(x.leading(ysize - 1));
        y.0[ysize - 1] = x_hi;

        // Unshift the remainder from the earlier adjustment
        y.shr_assign_limb_vartime(lshift);
    }

    /// Perform in-place division (`x` / `y`) for a pre-shifted dividend and divisor,
    /// tracking only the remainder.
    ///
    /// The dividend and divisor must be left-shifted such that the high bit of the divisor
    /// is set, and `x_hi` holds the top bits of the dividend.
    ///
    /// The shifted remainder is returned in `y`, and must be unshifted by the caller.
    /// `x` is left in an indeterminate state.
    #[inline(always)]
    const fn rem_wide_shifted(
        x: (&mut Self, &mut Self),
        mut x_hi: Limb,
        y: &mut Self,
        ywords: u32,
    ) {
        let (x_lo, x) = x;
        let ysize = y.nlimbs();

        // Calculate a reciprocal from the highest word of the divisor
        let reciprocal = Reciprocal::new(y.0[ysize - 1].to_nz().expect("zero divisor"));
        debug_assert!(reciprocal.shift() == 0);

        // Perform the core division algorithm
        x_hi = Self::rem_wide_large_shifted(
            (x_lo, x),
            x_hi,
            y,
            ywords,
            reciprocal,
            ConstChoice::FALSE,
        );

        // Calculate remainder for the case where the divisor is a single word.
        let limb_div = ConstChoice::from_u32_eq(1, ywords);
        // Note that `div2by1()` will panic if `x_hi >= reciprocal.divisor_normalized`,
        // but this can only be the case if `limb_div` is falsy, in which case we discard
        // the result anyway, so we conditionally set `x_hi` to zero for this branch.
        let x_hi_adjusted = Limb::select(Limb::ZERO, x_hi, limb_div);
        let (_, rem2) = div2by1(x_hi_adjusted.0, x.0[0].0, &reciprocal);

        // Copy out the low limb of the remainder
        y.0[0] = Limb::select(x.0[0], Limb(rem2), limb_div);

        // Copy the remainder to divisor
        let mut i = 1;
        while i < ysize {
            y.0[i] = Limb::select(
                Limb::ZERO,
                x.0[i],
                ConstChoice::from_u32_lt(i as u32, ywords),
            );
            y.0[i] = Limb::select(y.0[i], x_hi, ConstChoice::from_u32_eq(i as u32, ywords - 1));
            i += 1;
        }
    }

    /// Computes `x` % `y` for a 'large' divisor (>1 limbs), returning the remainder in `x.1`.
    ///
    /// While the divisor may only be a single limb, additional corrections to the result are
    /// required in this case.
    ///
    /// The dividend and divisor must be left-shifted such that the high bit of the divisor
    /// is set, and `x_hi` holds the top bits of the dividend.
    #[inline(always)]
    const fn rem_wide_large_shifted(
        x: (&Self, &mut Self),
        mut x_hi: Limb,
        y: &Self,
        ywords: u32,
        reciprocal: Reciprocal,
        vartime: ConstChoice,
    ) -> Limb {
        assert!(
            y.nlimbs() <= x.1.nlimbs(),
            "invalid input sizes for rem_wide_large_shifted"
        );

        let (x_lo, x) = x;
        let xsize = x.nlimbs();
        let ysize = y.nlimbs();
        let mut extra_limbs = x_lo.nlimbs();

        let mut xi = xsize - 1;
        let mut x_xi = x.0[xi];
        let mut i;
        let mut carry;

        // We proceed similarly to `div_rem_large_shifted()` applied to the high half of
        // the dividend, fetching the limbs from the lower part as we go.

        while xi > 0 {
            // Divide high dividend words by the high divisor word to estimate the quotient word
            let mut quo = div3by2(x_hi.0, x_xi.0, x.0[xi - 1].0, &reciprocal, y.0[ysize - 2].0);

            // This loop is a no-op once xi is smaller than the number of words in the divisor
            let done = ConstChoice::from_u32_lt(xi as u32, ywords - 1);
            if vartime.and(done).is_true_vartime() {
                break;
            }
            quo = done.select_word(quo, 0);

            // Subtract q*divisor from the dividend
            let borrow = {
                carry = Limb::ZERO;
                let mut borrow = Limb::ZERO;
                let mut tmp;
                i = (xi + 1).saturating_sub(ysize);
                while i <= xi {
                    (tmp, carry) =
                        y.0[ysize + i - xi - 1].carrying_mul_add(Limb(quo), carry, Limb::ZERO);
                    (x.0[i], borrow) = x.0[i].borrowing_sub(tmp, borrow);
                    i += 1;
                }
                (_, borrow) = x_hi.borrowing_sub(carry, borrow);
                borrow
            };

            // If the subtraction borrowed, then add back the divisor
            // The probability of this being needed is very low, about 2/(Limb::MAX+1)
            {
                let ct_borrow = ConstChoice::from_word_mask(borrow.0);
                carry = Limb::ZERO;
                i = (xi + 1).saturating_sub(ysize);
                while i <= xi {
                    (x.0[i], carry) = x.0[i].carrying_add(
                        Limb::select(Limb::ZERO, y.0[ysize + i - xi - 1], ct_borrow),
                        carry,
                    );
                    i += 1;
                }
            }

            // If we have lower limbs remaining, shift the dividend words one word left
            if extra_limbs > 0 {
                x_hi = x.0[xi];
                x_xi = x.0[xi - 1];
                extra_limbs -= 1;
                i = xi;
                while i > 0 {
                    x.0[i] = x.0[i - 1];
                    i -= 1;
                }
                x.0[0] = x_lo.0[extra_limbs];
            } else {
                x_hi = Limb::select(x.0[xi], x_hi, done);
                x_xi = Limb::select(x.0[xi - 1], x_xi, done);
                xi -= 1;
            }
        }

        x_hi
    }

    /// Divides `self` by the divisor encoded in the `reciprocal`, setting `self`
    /// to the quotient and returning the remainder.
    #[inline(always)]
    pub(crate) const fn div_rem_limb(&mut self, rhs: NonZero<Limb>) -> Limb {
        self.div_rem_limb_with_reciprocal(&Reciprocal::new(rhs))
    }

    /// Divides `self` by the divisor encoded in the `reciprocal`, setting `self`
    /// to the quotient and returning the remainder.
    #[inline(always)]
    pub(crate) const fn div_rem_limb_with_reciprocal(&mut self, reciprocal: &Reciprocal) -> Limb {
        let hi = self.shl_assign_limb(reciprocal.shift());
        self.div_rem_limb_with_reciprocal_shifted(hi, reciprocal)
    }

    /// Divides `self` by the divisor encoded in the `reciprocal`, setting `self`
    /// to the quotient and returning the remainder.
    #[inline(always)]
    pub(crate) const fn div_rem_limb_with_reciprocal_shifted(
        &mut self,
        mut hi: Limb,
        reciprocal: &Reciprocal,
    ) -> Limb {
        let mut j = self.0.len();
        while j > 0 {
            j -= 1;
            (self.0[j].0, hi.0) = div2by1(hi.0, self.0[j].0, reciprocal);
        }
        hi.shr(reciprocal.shift())
    }

    /// Divides `self` by the divisor encoded in the `reciprocal`, returning the remainder.
    #[inline(always)]
    pub(crate) const fn rem_limb(&self, rhs: NonZero<Limb>) -> Limb {
        self.rem_limb_with_reciprocal(&Reciprocal::new(rhs), Limb::ZERO)
    }

    /// Divides `self` by the divisor encoded in the `reciprocal`, and returns the remainder.
    pub(crate) const fn rem_limb_with_reciprocal(
        &self,
        reciprocal: &Reciprocal,
        carry: Limb,
    ) -> Limb {
        let nlimbs = self.nlimbs();
        if nlimbs == 0 {
            return carry;
        }
        let lshift = reciprocal.shift();
        let nz = ConstChoice::from_u32_nonzero(lshift);
        let rshift = nz.if_true_u32(Limb::BITS - lshift);
        let mut hi = (carry.0 << lshift) | nz.if_true_word(self.0[nlimbs - 1].0 >> rshift);
        let mut lo;
        let mut j = nlimbs;
        while j > 1 {
            j -= 1;
            lo = self.0[j].0 << lshift;
            lo |= nz.if_true_word(self.0[j - 1].0 >> rshift);
            (_, hi) = div2by1(hi, lo, reciprocal);
        }
        (_, hi) = div2by1(hi, self.0[0].0 << lshift, reciprocal);
        Limb(hi >> lshift)
    }
}
