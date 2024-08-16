//! Bernstein-Yang macros.

/// Write an impl of a limb conversion function.
///
/// Workaround for making this function generic around limb types while still allowing it to be
/// `const fn`.
macro_rules! impl_limb_convert {
    ($input_type:ty, $input_bits:expr, $input:expr, $output_type:ty, $output_bits:expr, $output:expr) => {{
        // This function is defined because the method "min" of the usize type is not constant
        const fn min(a: usize, b: usize) -> usize {
            if a > b {
                b
            } else {
                a
            }
        }

        let total = min($input.len() * $input_bits, $output.len() * $output_bits);
        let mut bits = 0;

        while bits < total {
            let (i, o) = (bits % $input_bits, bits % $output_bits);
            $output[bits / $output_bits] |= ($input[bits / $input_bits] >> i) as $output_type << o;
            bits += min($input_bits - i, $output_bits - o);
        }

        let mask = (<$output_type>::MAX as $output_type) >> (<$output_type>::BITS as usize - $output_bits);
        let mut filled = total / $output_bits + if total % $output_bits > 0 { 1 } else { 0 };

        while filled > 0 {
            filled -= 1;
            $output[filled] &= mask;
        }
    }};
}
