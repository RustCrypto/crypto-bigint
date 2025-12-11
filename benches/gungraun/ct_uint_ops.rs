use std::hint::black_box;

use crypto_bigint::U1024;
use gungraun::library_benchmark;

use super::utils::random_uint;

// Benchmark wrapping addition for U1024 with different operand patterns.
#[library_benchmark]
#[bench::zeros(U1024::ZERO, U1024::ZERO)]
#[bench::one_plus_max(U1024::ONE, U1024::MAX)]
#[bench::max_plus_one(U1024::MAX, U1024::ONE)]
#[bench::max_plus_max(U1024::MAX, U1024::MAX)]
#[bench::low_high_pattern(
    U1024::from_u128(0xFFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF),
    U1024::from_u128(0x0000_0000_0000_0000_0000_0000_0000_0002)
)]
#[bench::random_1(random_uint(1), random_uint(2))]
#[bench::random_2(random_uint(3), random_uint(4))]
#[bench::random_3(random_uint(5), random_uint(6))]
pub fn bench_u1024_wrapping_add(a: U1024, b: U1024) -> U1024 {
    black_box(a.wrapping_add(black_box(&b)))
}

// Benchmark wrapping subtraction for U1024 with different operand patterns.
#[library_benchmark]
#[bench::zeros(U1024::ZERO, U1024::ZERO)]
#[bench::one_minus_max(U1024::ONE, U1024::MAX)]
#[bench::max_minus_one(U1024::MAX, U1024::ONE)]
#[bench::max_minus_max(U1024::MAX, U1024::MAX)]
#[bench::low_high_pattern(
    U1024::from_u128(0xFFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF),
    U1024::from_u128(0x0000_0000_0000_0000_0000_0000_0000_0002)
)]
#[bench::random_1(random_uint(1), random_uint(2))]
#[bench::random_2(random_uint(3), random_uint(4))]
#[bench::random_3(random_uint(5), random_uint(6))]
pub fn bench_u1024_wrapping_sub(a: U1024, b: U1024) -> U1024 {
    black_box(a.wrapping_sub(&b))
}

// Benchmark wrapping multiplication for U1024 with different operand patterns.
#[library_benchmark]
#[bench::zeros(U1024::ZERO, U1024::ZERO)]
#[bench::one_times_max(U1024::ONE, U1024::MAX)]
#[bench::max_times_one(U1024::MAX, U1024::ONE)]
#[bench::max_times_max(U1024::MAX, U1024::MAX)]
#[bench::low_high_pattern(
    U1024::from_u128(0xFFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF),
    U1024::from_u128(0x0000_0000_0000_0000_0000_0000_0000_0002)
)]
#[bench::random_1(random_uint(1), random_uint(2))]
#[bench::random_2(random_uint(3), random_uint(4))]
#[bench::random_3(random_uint(5), random_uint(6))]
pub fn bench_u1024_wrapping_mul(a: U1024, b: U1024) -> U1024 {
    black_box(a.wrapping_mul(black_box(&b)))
}
