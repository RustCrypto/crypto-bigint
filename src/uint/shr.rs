//! [`Uint`] bitwise right shift operations.

use crate::{ConstChoice, ConstCtOption, Limb, ShrVartime, Uint, WrappingShr};
use core::ops::{Shr, ShrAssign};
use subtle::CtOption;

impl<const LIMBS: usize> Uint<LIMBS> {
    /// Constant time right shift, implemented in ARM assembly.
    #[allow(unsafe_code)]
    #[cfg(target_arch = "aarch64")]
    pub unsafe fn shr_asm(&self, shift: u32) -> Uint<LIMBS> {
        // Ensure shift is less than total bits.
        assert!(
            shift < Uint::<LIMBS>::BITS,
            "`shift` must be less than the bit size of the integer"
        );
        let mut res = Uint::ZERO;
        let limbs = self.as_limbs();
        let out_limbs = res.as_limbs_mut();

        // Split shift into whole‑limb and in‑limb parts.
        let limb_shift = (shift >> 6) as u64; // number of 64-bit limbs to shift
        let bit_shift = shift & 0x3F; // remaining bit shift (0..63)
        let total_limbs = LIMBS as u64;
        // A constant zero limb we can safely load when the index is out-of-range.
        let zero: u64 = 0;

        // We now loop over each output limb index i in 0..total_limbs.
        // For each output index i, compute:
        //    a = (if i+limb_shift < total_limbs then src[i+limb_shift] else 0)
        //    b = (if i+limb_shift+1 < total_limbs then src[i+limb_shift+1] else 0)
        //    result[i] = (if bit_shift != 0:
        //                      (a >> bit_shift) | (b << (64-bit_shift))
        //                  else:
        //                      a)
        unsafe {
            core::arch::asm!(
                // x0: pointer to input limbs (limbs.as_ptr())
                // x1: pointer to output limbs (out_limbs.as_mut_ptr())
                // x2: loop index i (0..total_limbs)
                // x3: bit_shift (0..63)
                // x4: limb_shift
                // x5: total_limbs
                // x12: pointer to a zero limb (&zero)
                "mov x2, #0",                // i = 0
                "1:",
                "cmp x2, x5",                // if i >= total_limbs, exit loop
                "b.ge 2f",

                // Compute a_index = i + limb_shift, store in x7.
                "add x7, x2, x4",            // x7 = i + limb_shift
                "lsl x8, x7, #3",            // x8 = (a_index * 8)
                "add x8, x0, x8",            // tentative pointer for a: src + (a_index * 8)
                "cmp x7, x5",                // if (i + limb_shift) < total_limbs?
                "csel x8, x8, x12, lt",       // if x7 < x5 then x8 remains; else use zero pointer

                // Compute b_index = i + limb_shift + 1.
                "add x7, x2, x4",            // x7 = i + limb_shift again
                "add x7, x7, #1",            // x7 = i + limb_shift + 1
                "lsl x9, x7, #3",            // x9 = (b_index * 8)
                "add x9, x0, x9",            // tentative pointer for b: src + (b_index * 8)
                "cmp x7, x5",                // if (i + limb_shift + 1) < total_limbs?
                "csel x9, x9, x12, lt",       // if true, keep; else use zero pointer

                // Load the limbs for a and b.
                "ldr x10, [x8]",             // x10 = a
                "ldr x11, [x9]",             // x11 = b

                // For bit shifting:
                // Compute part_a = a >> bit_shift.
                "lsr x10, x10, x3",          // x10 = a >> bit_shift

                // Compute part_b = b << (64 - bit_shift).
                "mov x6, #64",               // x6 = 64
                "sub x6, x6, x3",            // x6 = 64 - bit_shift
                "lsl x11, x11, x6",          // x11 = b << (64 - bit_shift)
                // If bit_shift is zero, force part_b to 0.
                "cmp x3, #0",
                "csel x11, xzr, x11, eq",     // if bit_shift == 0, x11 = 0

                // Combine the two parts.
                "orr x10, x10, x11",         // result = part_a OR part_b

                // Compute the output pointer for index i.
                "lsl x7, x2, #3",            // offset = i * 8
                "add x7, x1, x7",            // destination pointer = out + offset
                "str x10, [x7]",             // store result limb

                // Increment loop index.
                "add x2, x2, #1",
                "b 1b",
                "2:",
                in("x0") limbs.as_ptr(),         // input pointer
                in("x1") out_limbs.as_mut_ptr(),   // output pointer
                in("x3") bit_shift,                // bit shift value
                in("x4") limb_shift,               // limb shift value
                in("x5") total_limbs,              // total number of limbs
                in("x12") &zero,                   // pointer to a zero limb
                lateout("x2") _,                  // loop counter
                lateout("x6") _,                  // scratch for (64 - bit_shift)
                lateout("x7") _,                  // scratch for indices and offsets
                lateout("x8") _,                  // pointer for a
                lateout("x9") _,                  // pointer for b
                lateout("x10") _,                 // holds shifted a / result
                lateout("x11") _,                 // holds shifted b
                options(nostack)
            )
        };
        res
    }

    #[allow(unsafe_code)]
    #[cfg(target_arch = "aarch64")]
    // TODO(dp):This works for shift < 64 –– worth keeping?
    /// Constant time right shift, implemented in ARM assembly, only works for small shifts (<64).
    pub unsafe fn shr_asm_small_shift(self: &Uint<LIMBS>, shift: u32) -> Uint<LIMBS> {
        assert!(
            shift < Uint::<LIMBS>::BITS,
            "`shift` within the bit size of the integer"
        );
        let mut res = Uint::ZERO;
        let limbs = self.as_limbs();
        let out_limbs = res.as_limbs_mut();
        unsafe {
            core::arch::asm!(
            "mov x6, #0",           // Init carry

            // Reverse loop over the limbs (starting from high to low)
            "add x0, x0, x2, LSL #3",   // Move input pointer to end
            "add x1, x1, x2, LSL #3",   // Move output pointer to end

            "1:",
            "ldr x7, [x0, #-8]!",   // x7 ← Memory[x0 - 8], pre-decrement x0
            "mov x8, x7",           // x8 ← x7 (preserve original limb value)
            "lsr x7, x7, x3",       // Right shift x7 by x3 steps
            "orr x7, x7, x6",       // Combine with carry
            "str x7, [x1, #-8]!",   // Store shifted limb and pre-decrement x1
            "neg x9, x3",           // x9 ← -x3 (for shift amount adjustment)
            "lsl x6, x8, x9",       // Left shift original limb to extract carry
            "subs x2, x2, #1",      // Decrement counter
            "b.ne 1b",              // Loop if not zero

            // Register Operand Bindings
            inout("x0") limbs.as_ptr() => _, // Input pointer to source limbs
            inout("x1") out_limbs.as_mut_ptr() => _, // Output pointer for result limbs
            inout("x2") LIMBS => _, // Limb counter (positive decrementing)
            in("x3") shift,         // Shift amount
            out("x6") _,            // Carry register

            // Register Preservation
            clobber_abi("C"),
            options(nostack),
            );
        }
        res
    }

    /// Computes `self >> shift`.
    ///
    /// Panics if `shift >= Self::BITS`.
    pub const fn shr(&self, shift: u32) -> Self {
        self.overflowing_shr(shift)
            .expect("`shift` within the bit size of the integer")
    }

    /// Computes `self >> shift` in variable time.
    ///
    /// Panics if `shift >= Self::BITS`.
    pub const fn shr_vartime(&self, shift: u32) -> Self {
        self.overflowing_shr_vartime(shift)
            .expect("`shift` within the bit size of the integer")
    }

    /// Computes `self >> shift`.
    ///
    /// Returns `None` if `shift >= Self::BITS`.
    pub const fn overflowing_shr(&self, shift: u32) -> ConstCtOption<Self> {
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
                    .overflowing_shr_vartime(1 << i)
                    .expect("shift within range"),
                bit,
            );
            i += 1;
        }

        ConstCtOption::new(Uint::select(&result, &Self::ZERO, overflow), overflow.not())
    }

    /// Computes `self >> shift`.
    ///
    /// Returns `None` if `shift >= Self::BITS`.
    ///
    /// NOTE: this operation is variable time with respect to `shift` *ONLY*.
    ///
    /// When used with a fixed `shift`, this function is constant-time with respect
    /// to `self`.
    #[inline(always)]
    pub const fn overflowing_shr_vartime(&self, shift: u32) -> ConstCtOption<Self> {
        let mut limbs = [Limb::ZERO; LIMBS];

        if shift >= Self::BITS {
            return ConstCtOption::none(Self::ZERO);
        }

        let shift_num = (shift / Limb::BITS) as usize;
        let rem = shift % Limb::BITS;

        let mut i = 0;
        while i < LIMBS - shift_num {
            limbs[i] = self.limbs[i + shift_num];
            i += 1;
        }

        if rem == 0 {
            return ConstCtOption::some(Self { limbs });
        }

        let mut carry = Limb::ZERO;

        while i > 0 {
            i -= 1;
            let shifted = limbs[i].shr(rem);
            let new_carry = limbs[i].shl(Limb::BITS - rem);
            limbs[i] = shifted.bitor(carry);
            carry = new_carry;
        }

        ConstCtOption::some(Self { limbs })
    }

    /// Computes a right shift on a wide input as `(lo, hi)`.
    ///
    /// Returns `None` if `shift >= Self::BITS`.
    ///
    /// NOTE: this operation is variable time with respect to `shift` *ONLY*.
    ///
    /// When used with a fixed `shift`, this function is constant-time with respect
    /// to `self`.
    #[inline(always)]
    pub const fn overflowing_shr_vartime_wide(
        lower_upper: (Self, Self),
        shift: u32,
    ) -> ConstCtOption<(Self, Self)> {
        let (lower, upper) = lower_upper;
        if shift >= 2 * Self::BITS {
            ConstCtOption::none((Self::ZERO, Self::ZERO))
        } else if shift >= Self::BITS {
            let lower = upper
                .overflowing_shr_vartime(shift - Self::BITS)
                .expect("shift within range");
            ConstCtOption::some((lower, Self::ZERO))
        } else {
            let new_upper = upper
                .overflowing_shr_vartime(shift)
                .expect("shift within range");
            let lower_hi = upper
                .overflowing_shl_vartime(Self::BITS - shift)
                .expect("shift within range");
            let lower_lo = lower
                .overflowing_shr_vartime(shift)
                .expect("shift within range");
            ConstCtOption::some((lower_lo.bitor(&lower_hi), new_upper))
        }
    }

    /// Computes `self >> shift` in a panic-free manner, returning zero if the shift exceeds the
    /// precision.
    pub const fn wrapping_shr(&self, shift: u32) -> Self {
        self.overflowing_shr(shift).unwrap_or(Self::ZERO)
    }

    /// Computes `self >> shift` in variable-time in a panic-free manner, returning zero if the
    /// shift exceeds the precision.
    pub const fn wrapping_shr_vartime(&self, shift: u32) -> Self {
        self.overflowing_shr_vartime(shift).unwrap_or(Self::ZERO)
    }

    /// Computes `self >> 1` in constant-time.
    pub(crate) const fn shr1(&self) -> Self {
        self.shr1_with_carry().0
    }

    /// Computes `self >> 1` in constant-time, returning [`ConstChoice::TRUE`]
    /// if the least significant bit was set, and [`ConstChoice::FALSE`] otherwise.
    #[inline(always)]
    pub(crate) const fn shr1_with_carry(&self) -> (Self, ConstChoice) {
        let mut ret = Self::ZERO;
        let mut i = LIMBS;
        let mut carry = Limb::ZERO;
        while i > 0 {
            i -= 1;
            let (shifted, new_carry) = self.limbs[i].shr1();
            ret.limbs[i] = shifted.bitor(carry);
            carry = new_carry;
        }

        (ret, ConstChoice::from_word_lsb(carry.0 >> Limb::HI_BIT))
    }
}

macro_rules! impl_shr {
    ($($shift:ty),+) => {
        $(
            impl<const LIMBS: usize> Shr<$shift> for Uint<LIMBS> {
                type Output = Uint<LIMBS>;

                #[inline]
                fn shr(self, shift: $shift) -> Uint<LIMBS> {
                    #[allow(unsafe_code)]
                    unsafe{ self.shr_asm(u32::try_from(shift).expect("invalid shift"))}
                }
            }

            impl<const LIMBS: usize> Shr<$shift> for &Uint<LIMBS> {
                type Output = Uint<LIMBS>;

                #[inline]
                fn shr(self, shift: $shift) -> Uint<LIMBS> {
                    #[allow(unsafe_code)]
                    unsafe{self.shr_asm(u32::try_from(shift).expect("invalid shift"))}
                }
            }

            impl<const LIMBS: usize> ShrAssign<$shift> for Uint<LIMBS> {
                fn shr_assign(&mut self, shift: $shift) {
                    #[allow(unsafe_code)]
                    unsafe{*self = self.shr_asm(u32::try_from(shift).expect("invalid shift"))}
                }
            }
        )+
    };
}

impl_shr!(i32, u32, usize);

impl<const LIMBS: usize> WrappingShr for Uint<LIMBS> {
    fn wrapping_shr(&self, shift: u32) -> Uint<LIMBS> {
        self.wrapping_shr(shift)
    }
}

impl<const LIMBS: usize> ShrVartime for Uint<LIMBS> {
    fn overflowing_shr_vartime(&self, shift: u32) -> CtOption<Self> {
        self.overflowing_shr(shift).into()
    }
    fn wrapping_shr_vartime(&self, shift: u32) -> Self {
        self.wrapping_shr(shift)
    }
}

#[cfg(test)]
mod tests {
    use crate::{U64, U128, U256, Uint};

    const N: U256 =
        U256::from_be_hex("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141");

    const N_2: U256 =
        U256::from_be_hex("7FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF5D576E7357A4501DDFE92F46681B20A0");

    const SIXTY_FIVE: U256 =
        U256::from_be_hex("00000000000000007FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF5D576E7357A4501D");

    const EIGHTY_EIGHT: U256 =
        U256::from_be_hex("0000000000000000000000FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF");

    const SIXTY_FOUR: U256 =
        U256::from_be_hex("0000000000000000FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03B");

    #[test]
    fn shr_simple() {
        let mut t = U256::from(2u8);
        assert_eq!(t >> 1, U256::from(1u8));
        t = U256::from(0x300u16);
        assert_eq!(t >> 8, U256::from(3u8));
    }

    #[test]
    fn shr1() {
        assert_eq!(N.shr1(), N_2, "1-bit right shift, specialized");
        assert_eq!(N >> 1, N_2, "1-bit right shift, general");
    }

    #[test]
    fn shr_one() {
        let x = U64::from_be_hex("0000000000000002");
        let expected = U64::from_be_hex("0000000000000001");
        assert_eq!(
            x >> 1,
            expected,
            "\nx: {x:0b}, \nexpected \n{expected:0b}, got \n{:0b}",
            x >> 1,
        );
    }
    #[test]
    fn shr_2() {
        let x = U128::from_be_hex("ffffffffffffffffffffffffffffffff");
        let expected = x.overflowing_shr(1).unwrap();
        assert_eq!(
            x >> 1,
            expected,
            "\nx: {x:0b}, \nexpected \n{expected:0b}, got \n{:0b}",
            x >> 1,
        );
    }

    #[test]
    fn shr65() {
        assert_eq!(N.overflowing_shr_vartime(65).unwrap(), SIXTY_FIVE);
        assert_eq!(N >> 65, SIXTY_FIVE);
    }

    #[allow(unsafe_code)]
    #[test]
    fn shr_asm() {
        let x =
            U256::from_be_hex("FFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD03641410000000000000000");
        let shift = 64;
        let y = unsafe { x.shr_asm(shift) };
        let expected =
            U256::from_be_hex("0000000000000000FFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141");
        assert_eq!(y, expected);
    }

    #[test]
    fn shr88() {
        assert_eq!(N.overflowing_shr_vartime(88).unwrap(), EIGHTY_EIGHT);
        assert_eq!(N >> 88, EIGHTY_EIGHT);
    }

    #[test]
    fn shr256_const() {
        assert!(N.overflowing_shr(256).is_none().is_true_vartime());
        assert!(N.overflowing_shr_vartime(256).is_none().is_true_vartime());
    }

    #[test]
    #[should_panic(expected = "`shift` must be less than the bit size of the integer")]
    fn shr256() {
        let _ = N >> 256;
    }

    #[test]
    fn shr64() {
        assert_eq!(N.overflowing_shr_vartime(64).unwrap(), SIXTY_FOUR);
        assert_eq!(N >> 64, SIXTY_FOUR);
    }

    #[test]
    fn shr_wide_1_1_128() {
        assert_eq!(
            Uint::overflowing_shr_vartime_wide((U128::ONE, U128::ONE), 128).unwrap(),
            (U128::ONE, U128::ZERO)
        );
    }

    #[test]
    fn shr_wide_0_max_1() {
        assert_eq!(
            Uint::overflowing_shr_vartime_wide((U128::ZERO, U128::MAX), 1).unwrap(),
            (U128::ONE << 127, U128::MAX >> 1)
        );
    }

    #[test]
    fn shr_wide_max_max_256() {
        assert!(
            Uint::overflowing_shr_vartime_wide((U128::MAX, U128::MAX), 256)
                .is_none()
                .is_true_vartime()
        );
    }
}
