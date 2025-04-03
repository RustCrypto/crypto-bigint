//! [`Uint`] bitwise left shift operations.

use crate::{ConstChoice, ConstCtOption, Limb, ShlVartime, Uint, Word, WrappingShl};
use core::ops::{Shl, ShlAssign};
use subtle::CtOption;

impl<const LIMBS: usize> Uint<LIMBS> {
    /// Constant time left shift, implemented in ARM assembly.
    #[allow(unsafe_code)]
    #[cfg(target_arch = "aarch64")]
    pub unsafe fn shl_asm(self: &Uint<LIMBS>, shift: u32) -> Uint<LIMBS> {
        // Total bits in the multi‑precision integer.
        assert!(
            shift < Uint::<LIMBS>::BITS,
            "`shift` within the bit size of the integer"
        );
        let mut res = Uint::ZERO;
        let limbs = self.as_limbs();
        let out_limbs = res.as_limbs_mut();

        // Split the shift into whole-limb and in-limb parts.
        let limb_shift = (shift >> 6) as u64; // how many 64‑bit limbs to shift by
        let bit_shift = shift & 0x3F; // remaining bit shift in [0,63]
        let total_limbs = LIMBS as u64;
        // A constant zero limb we can load from.
        let zero: u64 = 0;

        // Loop over each output limb index (0 <= i < total_limbs)
        // For each i, we want to compute:
        //   j = i - limb_shift,
        //   a = (j >= 0) ? src[j] : 0,
        //   b = (j-1 >= 0) ? src[j-1] : 0,
        //   out[i] = (a << bit_shift) | (if bit_shift != 0 { b >> (64 - bit_shift) } else { 0 }).
        //
        // This implementation is constant time by always iterating all limbs and using
        // conditional select (csel) to avoid branches.
        unsafe {
            core::arch::asm!(
                // x0: pointer to input limbs (limbs.as_ptr())
                // x1: pointer to output limbs (out_limbs.as_mut_ptr())
                // x2: loop index i (0 <= i < total_limbs)
                // x3: bit_shift
                // x4: limb_shift
                // x5: total_limbs
                // x12: pointer to a zero limb (&zero)
                "mov x2, #0",                // i = 0
                "1:",
                "cmp x2, x5",                // if i >= total_limbs, exit loop
                "b.ge 2f",

                // Compute j = i - limb_shift into x7 (as signed)
                "sub x7, x2, x4",            // x7 = i - limb_shift
                // Compute a_ptr = (j >= 0) ? (src + (j << 3)) : zero_ptr
                "lsl x8, x7, #3",            // x8 = j * 8
                "add x8, x0, x8",            // tentative a_ptr = src + (j * 8)
                "cmp x7, #0",                // test if j < 0
                "csel x8, x12, x8, lt",       // if j < 0, set a_ptr = zero_ptr

                // Compute j2 = i - limb_shift - 1 into x7 again.
                "sub x7, x2, x4",            // x7 = i - limb_shift
                "subs x7, x7, #1",           // x7 = i - limb_shift - 1
                // Compute b_ptr = (j2 >= 0) ? (src + (j2 << 3)) : zero_ptr
                "lsl x9, x7, #3",            // x9 = j2 * 8
                "add x9, x0, x9",            // tentative b_ptr = src + (j2 * 8)
                "cmp x7, #0",                // test if j2 < 0
                "csel x9, x12, x9, lt",       // if j2 < 0, set b_ptr = zero_ptr

                // Load limbs a and b.
                "ldr x10, [x8]",             // x10 = a
                "ldr x11, [x9]",             // x11 = b

                // Compute part_a = a << bit_shift.
                "lsl x10, x10, x3",          // x10 = a << bit_shift

                // Compute part_b = b >> (64 - bit_shift).
                "mov x6, #64",               // prepare constant 64
                "sub x6, x6, x3",            // x6 = 64 - bit_shift (note: if x3==0, x6 becomes 64)
                "lsr x11, x11, x6",          // x11 = b >> (64 - bit_shift)
                // If bit_shift is 0, force part_b to 0 (since a >> 64 would be undefined).
                "cmp x3, #0",
                "csel x11, xzr, x11, eq",     // if bit_shift == 0, set x11 = 0

                // Combine parts: result = part_a OR part_b.
                "orr x10, x10, x11",

                // Store the result in out[i]. Compute the address: out_ptr + (i * 8).
                "lsl x7, x2, #3",            // offset = i * 8
                "add x7, x1, x7",            // destination pointer = out_ptr + offset
                "str x10, [x7]",             // store the computed limb

                // Increment loop counter and repeat.
                "add x2, x2, #1",
                "b 1b",
                "2:",
                in("x0") limbs.as_ptr(),         // input pointer
                in("x1") out_limbs.as_mut_ptr(),   // output pointer
                in("x3") bit_shift,                // bit shift amount
                in("x4") limb_shift,               // limb shift amount
                in("x5") total_limbs,              // total limbs
                in("x12") &zero,                   // pointer to zero limb
                lateout("x2") _,                  // loop index
                lateout("x6") _,                  // temporary for (64 - bit_shift)
                lateout("x7") _,                  // scratch (offset and index calculations)
                lateout("x8") _,                  // pointer for a
                lateout("x9") _,                  // pointer for b
                lateout("x10") _,                 // holds part_a (and then combined result)
                lateout("x11") _,                 // holds part_b
                options(nostack)
            )
        };
        res
    }

    // TODO(dp):This works for shift < 64 –– worth keeping?
    /// Constant time left shift, implemented in ARM assembly, only works for small shifts (<64).
    #[allow(unsafe_code, unused)]
    pub unsafe fn shl_asm_small_shift(&self, shift: u32) -> Uint<LIMBS> {
        assert!(shift < Uint::<LIMBS>::BITS, "Shift out of bounds");
        let mut res = Uint::ZERO;
        let limbs = self.as_limbs();
        let out_limbs = res.as_limbs_mut();

        unsafe {
            core::arch::asm!(
            "mov x6, #0",           // Init carry

            // Forward loop over the limbs (starting from low to high)
            "1:",
            "ldr x7, [x0], #8",    // x7 ← Memory[x0], post-increment x0
            "mov x8, x7",          // x8 ← x7 (preserve original limb value)
            "lsl x7, x7, x3",      // Left shift x7 by x3 steps
            "orr x7, x7, x6",      // Combine with carry
            "str x7, [x1], #8",    // Store shifted limb and post-increment x1
            "neg x9, x3",          // x9 ← -x3 (for shift amount adjustment)
            "lsr x6, x8, x9",      // Right shift original limb to extract carry
            "subs x2, x2, #1",     // Decrement counter
            "b.ne 1b",             // Loop if not zero

            // Register Operand Bindings
            inout("x0") limbs.as_ptr() => _, // Input pointer to source limbs
            inout("x1") out_limbs.as_mut_ptr() => _, // Output pointer for result limbs
            inout("x2") LIMBS => _, // Limb counter
            in("x3") shift,         // Shift amount
            out("x6") _,            // Carry register

            // Register Preservation
            clobber_abi("C"),
            options(nostack),
            );
        }
        res
    }

    /// Computes `self << shift`.
    ///
    /// Panics if `shift >= Self::BITS`.
    pub const fn shl(&self, shift: u32) -> Self {
        self.overflowing_shl(shift)
            .expect("`shift` within the bit size of the integer")
    }

    /// Computes `self << shift` in variable time.
    ///
    /// Panics if `shift >= Self::BITS`.
    pub const fn shl_vartime(&self, shift: u32) -> Self {
        self.overflowing_shl_vartime(shift)
            .expect("`shift` within the bit size of the integer")
    }

    /// Computes `self << shift`.
    ///
    /// Returns `None` if `shift >= Self::BITS`.
    pub const fn overflowing_shl(&self, shift: u32) -> ConstCtOption<Self> {
        // `floor(log2(BITS - 1))` is the number of bits in the representation of `shift`
        // (which lies in range `0 <= shift < BITS`).
        let shift_bits = u32::BITS - (Self::BITS - 1).leading_zeros();
        let overflow = ConstChoice::from_u32_lt(shift, Self::BITS).not();
        let shift = shift % Self::BITS;
        let mut result = *self;
        let mut i = 0;
        while i < shift_bits {
            let bit = ConstChoice::from_u32_lsb((shift >> i) & 1);
            result = Uint::select(
                &result,
                &result
                    .overflowing_shl_vartime(1 << i)
                    .expect("shift within range"),
                bit,
            );
            i += 1;
        }

        ConstCtOption::new(Uint::select(&result, &Self::ZERO, overflow), overflow.not())
    }

    /// Computes `self << shift`.
    ///
    /// Returns `None` if `shift >= Self::BITS`.
    ///
    /// NOTE: this operation is variable time with respect to `shift` *ONLY*.
    ///
    /// When used with a fixed `shift`, this function is constant-time with respect
    /// to `self`.
    #[inline(always)]
    pub const fn overflowing_shl_vartime(&self, shift: u32) -> ConstCtOption<Self> {
        let mut limbs = [Limb::ZERO; LIMBS];

        if shift >= Self::BITS {
            return ConstCtOption::none(Self::ZERO);
        }

        let shift_num = (shift / Limb::BITS) as usize;
        let rem = shift % Limb::BITS;

        let mut i = shift_num;
        while i < LIMBS {
            limbs[i] = self.limbs[i - shift_num];
            i += 1;
        }

        if rem == 0 {
            return ConstCtOption::some(Self { limbs });
        }

        let mut carry = Limb::ZERO;

        let mut i = shift_num;
        while i < LIMBS {
            let shifted = limbs[i].shl(rem);
            let new_carry = limbs[i].shr(Limb::BITS - rem);
            limbs[i] = shifted.bitor(carry);
            carry = new_carry;
            i += 1;
        }

        ConstCtOption::some(Self { limbs })
    }

    /// Computes a left shift on a wide input as `(lo, hi)`.
    ///
    /// Returns `None` if `shift >= Self::BITS`.
    ///
    /// NOTE: this operation is variable time with respect to `shift` *ONLY*.
    ///
    /// When used with a fixed `shift`, this function is constant-time with respect
    /// to `self`.
    #[inline(always)]
    pub const fn overflowing_shl_vartime_wide(
        lower_upper: (Self, Self),
        shift: u32,
    ) -> ConstCtOption<(Self, Self)> {
        let (lower, upper) = lower_upper;
        if shift >= 2 * Self::BITS {
            ConstCtOption::none((Self::ZERO, Self::ZERO))
        } else if shift >= Self::BITS {
            let upper = lower
                .overflowing_shl_vartime(shift - Self::BITS)
                .expect("shift within range");
            ConstCtOption::some((Self::ZERO, upper))
        } else {
            let new_lower = lower
                .overflowing_shl_vartime(shift)
                .expect("shift within range");
            let upper_lo = lower
                .overflowing_shr_vartime(Self::BITS - shift)
                .expect("shift within range");
            let upper_hi = upper
                .overflowing_shl_vartime(shift)
                .expect("shift within range");
            ConstCtOption::some((new_lower, upper_lo.bitor(&upper_hi)))
        }
    }

    /// Computes `self << shift` in a panic-free manner, returning zero if the shift exceeds the
    /// precision.
    pub const fn wrapping_shl(&self, shift: u32) -> Self {
        self.overflowing_shl(shift).unwrap_or(Self::ZERO)
    }

    /// Computes `self << shift` in variable-time in a panic-free manner, returning zero if the
    /// shift exceeds the precision.
    pub const fn wrapping_shl_vartime(&self, shift: u32) -> Self {
        self.overflowing_shl_vartime(shift).unwrap_or(Self::ZERO)
    }

    /// Computes `self << shift` where `0 <= shift < Limb::BITS`,
    /// returning the result and the carry.
    #[inline(always)]
    pub(crate) const fn shl_limb(&self, shift: u32) -> (Self, Limb) {
        let mut limbs = [Limb::ZERO; LIMBS];

        let nz = ConstChoice::from_u32_nonzero(shift);
        let lshift = shift;
        let rshift = nz.if_true_u32(Limb::BITS - shift);
        let carry = nz.if_true_word(self.limbs[LIMBS - 1].0.wrapping_shr(Word::BITS - shift));

        limbs[0] = Limb(self.limbs[0].0 << lshift);
        let mut i = 1;
        while i < LIMBS {
            let mut limb = self.limbs[i].0 << lshift;
            let hi = self.limbs[i - 1].0 >> rshift;
            limb |= nz.if_true_word(hi);
            limbs[i] = Limb(limb);
            i += 1
        }

        (Uint::<LIMBS>::new(limbs), Limb(carry))
    }

    /// Computes `self << 1` in constant-time, returning [`ConstChoice::TRUE`]
    /// if the most significant bit was set, and [`ConstChoice::FALSE`] otherwise.
    #[inline(always)]
    pub(crate) const fn overflowing_shl1(&self) -> (Self, Limb) {
        let mut ret = Self::ZERO;
        let mut i = 0;
        let mut carry = Limb::ZERO;
        while i < LIMBS {
            let (shifted, new_carry) = self.limbs[i].shl1();
            ret.limbs[i] = shifted.bitor(carry);
            carry = new_carry;
            i += 1;
        }

        (ret, carry)
    }
}

macro_rules! impl_shl {
    ($($shift:ty),+) => {
        $(
            impl<const LIMBS: usize> Shl<$shift> for Uint<LIMBS> {
                type Output = Uint<LIMBS>;

                #[inline]
                fn shl(self, shift: $shift) -> Uint<LIMBS> {
                    #[allow(unsafe_code)]
                    unsafe{
                        self.shl_asm(u32::try_from(shift).expect("invalid shift"))
                    }
                }
            }

            impl<const LIMBS: usize> Shl<$shift> for &Uint<LIMBS> {
                type Output = Uint<LIMBS>;

                #[inline]
                fn shl(self, shift: $shift) -> Uint<LIMBS> {
                    #[allow(unsafe_code)]
                    unsafe {
                        self.shl_asm(u32::try_from(shift).expect("invalid shift"))
                    }
                }
            }

            impl<const LIMBS: usize> ShlAssign<$shift> for Uint<LIMBS> {
                fn shl_assign(&mut self, shift: $shift) {
                    #[allow(unsafe_code)]
                    unsafe {
                        *self = self.shl_asm(u32::try_from(shift).expect("invalid shift"))
                    }
                }
            }
        )+
    };
}

impl_shl!(i32, u32, usize);

impl<const LIMBS: usize> WrappingShl for Uint<LIMBS> {
    fn wrapping_shl(&self, shift: u32) -> Uint<LIMBS> {
        self.wrapping_shl(shift)
    }
}

impl<const LIMBS: usize> ShlVartime for Uint<LIMBS> {
    fn overflowing_shl_vartime(&self, shift: u32) -> CtOption<Self> {
        self.overflowing_shl(shift).into()
    }
    fn wrapping_shl_vartime(&self, shift: u32) -> Self {
        self.wrapping_shl(shift)
    }
}

#[cfg(test)]
mod tests {
    use crate::{Limb, U128, U256, Uint};

    const N: U256 =
        U256::from_be_hex("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141");

    const TWO_N: U256 =
        U256::from_be_hex("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFD755DB9CD5E9140777FA4BD19A06C8282");

    const FOUR_N: U256 =
        U256::from_be_hex("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFAEABB739ABD2280EEFF497A3340D90504");

    const SIXTY_FIVE: U256 =
        U256::from_be_hex("FFFFFFFFFFFFFFFD755DB9CD5E9140777FA4BD19A06C82820000000000000000");

    const EIGHTY_EIGHT: U256 =
        U256::from_be_hex("FFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD03641410000000000000000000000");

    const SIXTY_FOUR: U256 =
        U256::from_be_hex("FFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD03641410000000000000000");

    #[test]
    fn shl_simple() {
        let mut t = U256::from(1u8);
        assert_eq!(t << 1, U256::from(2u8));
        t = U256::from(3u8);
        assert_eq!(t << 8, U256::from(0x300u16));
    }

    #[test]
    fn shl1() {
        assert_eq!(N << 1, TWO_N);
        assert_eq!(N.overflowing_shl1(), (TWO_N, Limb::ONE));
    }

    #[test]
    fn shl2() {
        assert_eq!(N << 2, FOUR_N);
    }

    #[test]
    fn shl65() {
        assert_eq!(N << 65, SIXTY_FIVE);
    }

    #[test]
    fn shl88() {
        assert_eq!(N << 88, EIGHTY_EIGHT);
    }

    #[test]
    fn shl256_const() {
        assert!(N.overflowing_shl(256).is_none().is_true_vartime());
        assert!(N.overflowing_shl_vartime(256).is_none().is_true_vartime());
    }

    #[test]
    #[should_panic(expected = "`shift` within the bit size of the integer")]
    fn shl256() {
        let _ = N << 256;
    }

    #[test]
    fn shl64() {
        assert_eq!(N << 64, SIXTY_FOUR);
    }

    #[test]
    fn shl_wide_1_1_128() {
        assert_eq!(
            Uint::overflowing_shl_vartime_wide((U128::ONE, U128::ONE), 128).unwrap(),
            (U128::ZERO, U128::ONE)
        );
        assert_eq!(
            Uint::overflowing_shl_vartime_wide((U128::ONE, U128::ONE), 128).unwrap(),
            (U128::ZERO, U128::ONE)
        );
    }

    #[test]
    fn shl_wide_max_0_1() {
        assert_eq!(
            Uint::overflowing_shl_vartime_wide((U128::MAX, U128::ZERO), 1).unwrap(),
            (U128::MAX.sbb(&U128::ONE, Limb::ZERO).0, U128::ONE)
        );
    }

    #[test]
    fn shl_wide_max_max_256() {
        assert!(
            Uint::overflowing_shl_vartime_wide((U128::MAX, U128::MAX), 256)
                .is_none()
                .is_true_vartime(),
        );
    }
}
