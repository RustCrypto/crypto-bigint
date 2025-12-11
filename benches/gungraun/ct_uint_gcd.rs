use std::hint::black_box;

use crypto_bigint::{Gcd, U1024};
use gungraun::library_benchmark;

use super::utils::random_uint;

// Constant-time GCD via the `Gcd` trait.
#[library_benchmark]
#[bench::zeros(U1024::ZERO, U1024::ZERO)]
#[bench::one_and_zero(U1024::ONE, U1024::ZERO)]
#[bench::max_and_one(U1024::MAX, U1024::ONE)]
#[bench::random_1(random_uint(1), random_uint(2))]
#[bench::random_2(random_uint(3), random_uint(4))]
#[bench::random_3(random_uint(5), random_uint(6))]
pub fn bench_u1024_gcd(a: U1024, b: U1024) -> U1024 {
    black_box(a.gcd(black_box(&b)))
}
