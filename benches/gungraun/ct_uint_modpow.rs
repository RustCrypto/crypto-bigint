use std::hint::black_box;

use crypto_bigint::{Odd, U1024, modular::MontyForm};
use gungraun::library_benchmark;

use super::utils::random_uint;

fn modpow_cases() -> Vec<(U1024, U1024, Odd<U1024>)> {
    let values = [U1024::ZERO, U1024::ONE, U1024::MAX, random_uint(1)];

    // Reuse the same value candidates as potential moduli, but keep only
    // odd, non-zero ones.
    let mut moduli = Vec::<Odd<U1024>>::new();
    for &n in &values {
        let candidate = Odd::new(n);
        if bool::from(candidate.is_some()) {
            moduli.push(candidate.unwrap());
        }
    }

    let mut cases = Vec::new();
    for &base in &values {
        for &exp in &values {
            for &m in &moduli {
                cases.push((base, exp, m));
            }
        }
    }

    cases
}

// Benchmark modular exponentiation using Montgomery form (`MontyForm::pow`) for U1024.
#[library_benchmark]
#[benches::with_iter(iter = modpow_cases())]
pub fn bench_u1024_modpow((base, exponent, modulus): (U1024, U1024, Odd<U1024>)) -> U1024 {
    let base = black_box(base);
    let exponent = black_box(exponent);
    let modulus = black_box(modulus);
    let params = black_box(crypto_bigint::modular::MontyParams::new(modulus));
    let base_monty = black_box(MontyForm::new(&base, params));
    black_box(base_monty.pow(&exponent).retrieve())
}
