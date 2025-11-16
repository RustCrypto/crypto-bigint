use std::hint::black_box;

use crypto_bigint::{BitOps, U1024};
use gungraun::library_benchmark;

use super::utils::random_uint;

fn high_bit_u1024() -> U1024 {
    let mut x = U1024::ZERO;
    x.set_bit_vartime(U1024::BITS - 1, true);
    x
}

// Benchmark variable-time comparison for U1024 with different operand patterns.
#[library_benchmark]
#[bench::equal(U1024::ZERO, U1024::ZERO)]
#[bench::diff_low(U1024::ONE, U1024::ZERO)]
#[bench::diff_high(high_bit_u1024(), U1024::ZERO)]
#[bench::random_1(random_uint(1), random_uint(2))]
#[bench::random_2(random_uint(3), random_uint(4))]
#[bench::random_3(random_uint(5), random_uint(6))]
pub fn bench_u1024_cmp_vartime(a: U1024, b: U1024) -> core::cmp::Ordering {
    black_box(a.cmp_vartime(&b))
}
