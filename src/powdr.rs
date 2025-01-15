#![allow(unsafe_code)]
use powdr_riscv_runtime::arith::{modmul_256_u8_le, modmul_256_u32_le};
// use zeroize::Zeroize;
use crate::{encoding::uint_to_le_bytes, Encoding, Uint, U256};
use subtle::ConstantTimeLess;
use core::mem;

/// Powdr supports BigInt operations with a width of 256-bits as 8x32-bit words.
pub(crate) const BIGINT_WIDTH_WORDS: usize = 8;

/// Modular multiplication of two 256-bit Uint values using the Powdr accelerator.
/// Returns the fully reduced and normalized modular multiplication result.
///
/// NOTE: This method takes generic Uint values, but asserts that the input is 256 bits. It is
/// provided because the main places we want to patch in multiplication use the generic Uint type,
/// and specialization is not a stable Rust feature. When inlined, the assert should be removed.
#[inline(always)]
pub(crate) fn modmul_uint_256<const LIMBS: usize>(
    a: &Uint<LIMBS>,
    b: &Uint<LIMBS>,
    modulus: &Uint<LIMBS>,
) -> Uint<LIMBS> {
    // Assert that we are working with 8x32 Uints.
    assert!(LIMBS == BIGINT_WIDTH_WORDS);

    // Convert to arrays of size 8 using slices
    let a_words: [u32; 8] = a.to_words()[..8].try_into().expect("Array size mismatch");
    let b_words: [u32; 8] = b.to_words()[..8].try_into().expect("Array size mismatch");
    let modulus_words: [u32; 8] = modulus.to_words()[..8].try_into().expect("Array size mismatch");

    // Perform modular multiplication
    let result_words = unsafe { modmul_256_u32_le(a_words, b_words, modulus_words) };

    // Convert the result back to Uint<LIMBS>
    let mut result_array = [0u32; LIMBS];
    result_array[..8].copy_from_slice(&result_words);

  
    // Convert back to Uint<LIMBS>
    let result = Uint::<LIMBS>::from_words(result_array);

    // Assert that the Prover returned the canonical representation of the result, i.e. that it
    // is fully reduced and has no multiples of the modulus included.
    // NOTE: On a cooperating prover, this check will always evaluate to false, and therefore
    // will have timing invariant with any secrets. If the prover is faulty, this check may
    // leak secret information through timing, however this is out of scope since a faulty
    // cannot be relied upon for the privacy of the inputs.
    assert!(bool::from(result.ct_lt(&modulus)));
    result
}

/// Modular multiplication of two 256-bit Uint values using the Powdr accelerator.
/// Returns a result in the equivelence class of integers under the modulus, but the result is not
/// guarenteed to be fully reduced. In particular, it may include any number of multiples of the
/// modulus.
#[inline(always)]
pub fn modmul_u256_denormalized(a: &U256, b: &U256, modulus: &U256) -> U256 {
    U256::from_le_bytes(unsafe {
      modmul_256_u8_le(
            a.to_le_bytes(),
            b.to_le_bytes(),
            modulus.to_le_bytes(),
        )
    })
}

/// Modular multiplication of two 256-bit Uint values using the Powdr accelerator.
/// Returns the fully reduced and normalized modular multiplication result.
#[inline(always)]
pub fn modmul_u256(a: &U256, b: &U256, modulus: &U256) -> U256 {
    let result = modmul_u256_denormalized(a, b, modulus);
    // Assert that the Prover returned the canonical representation of the result, i.e. that it
    // is fully reduced and has no multiples of the modulus included.
    // NOTE: On a cooperating prover, this check will always evaluate to false, and therefore
    // will have timing invariant with any secrets. If the prover is faulty, this check may
    // leak secret information through timing, however this is out of scope since a faulty
    // cannot be relied upon for the privacy of the inputs.
    assert!(bool::from(result.ct_lt(&modulus)));
    result
}

// fn convert_le_u64_to_u32<const LIMBS: usize>(input: [u64; LIMBS]) -> [u32; LIMBS * 2] {
//   let mut output = [0u32; LIMBS * 2];

//   for (i, &val) in input.iter().enumerate() {
//       // Extract the lower 32 bits and the upper 32 bits of the u64 value
//       output[i * 2] = (val & 0xFFFF_FFFF) as u32;      // Lower 32 bits
//       output[i * 2 + 1] = (val >> 32) as u32;          // Upper 32 bits
//   }

//   output
// }

// fn convert_le_u32_to_u64<const LIMBS: usize>(input: [u32; LIMBS * 2]) -> [u64; LIMBS] {
//   let mut output = [0u64; LIMBS];

//   for i in 0..LIMBS {
//       // Combine two u32 values into a single u64 value
//       let low = input[i * 2] as u64;
//       let high = (input[i * 2 + 1] as u64) << 32;
//       output[i] = low | high;
//   }

//   output
// }
