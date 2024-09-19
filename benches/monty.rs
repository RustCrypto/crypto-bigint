use criterion::{
    black_box, criterion_group, criterion_main, measurement::Measurement, BatchSize,
    BenchmarkGroup, Criterion,
};
use crypto_bigint::{
    modular::{MontyForm, MontyParams},
    Invert, Inverter, Odd, PrecomputeInverter, Random, RandomMod, U256,
};
use rand_core::OsRng;

#[cfg(feature = "alloc")]
use crypto_bigint::MultiExponentiate;

fn bench_montgomery_conversion<M: Measurement>(group: &mut BenchmarkGroup<'_, M>) {
    group.bench_function("MontyParams::new", |b| {
        b.iter_batched(
            || Odd::<U256>::random(&mut OsRng),
            |modulus| black_box(MontyParams::new(modulus)),
            BatchSize::SmallInput,
        )
    });

    group.bench_function("MontyParams::new_vartime", |b| {
        b.iter_batched(
            || Odd::<U256>::random(&mut OsRng),
            |modulus| black_box(MontyParams::new_vartime(modulus)),
            BatchSize::SmallInput,
        )
    });

    let params = MontyParams::new_vartime(Odd::<U256>::random(&mut OsRng));
    group.bench_function("MontyForm::new", |b| {
        b.iter_batched(
            || U256::random_mod(&mut OsRng, params.modulus().as_nz_ref()),
            |x| black_box(MontyForm::new(&x, params)),
            BatchSize::SmallInput,
        )
    });

    let params = MontyParams::new_vartime(Odd::<U256>::random(&mut OsRng));
    group.bench_function("MontyForm retrieve", |b| {
        b.iter_batched(
            || {
                MontyForm::new(
                    &U256::random_mod(&mut OsRng, params.modulus().as_nz_ref()),
                    params,
                )
            },
            |x| black_box(x.retrieve()),
            BatchSize::SmallInput,
        )
    });
}

fn bench_montgomery_ops<M: Measurement>(group: &mut BenchmarkGroup<'_, M>) {
    let params = MontyParams::new_vartime(Odd::<U256>::random(&mut OsRng));

    group.bench_function("add, U256", |b| {
        b.iter_batched(
            || {
                let a = MontyForm::new(
                    &U256::random_mod(&mut OsRng, params.modulus().as_nz_ref()),
                    params,
                );
                let b = MontyForm::new(
                    &U256::random_mod(&mut OsRng, params.modulus().as_nz_ref()),
                    params,
                );
                (a, b)
            },
            |(a, b)| black_box(a).add(&black_box(b)),
            BatchSize::SmallInput,
        )
    });

    group.bench_function("double, U256", |b| {
        b.iter_batched(
            || {
                MontyForm::new(
                    &U256::random_mod(&mut OsRng, params.modulus().as_nz_ref()),
                    params,
                )
            },
            |a| black_box(a).double(),
            BatchSize::SmallInput,
        )
    });

    group.bench_function("sub, U256", |b| {
        b.iter_batched(
            || {
                let a = MontyForm::new(
                    &U256::random_mod(&mut OsRng, params.modulus().as_nz_ref()),
                    params,
                );
                let b = MontyForm::new(
                    &U256::random_mod(&mut OsRng, params.modulus().as_nz_ref()),
                    params,
                );
                (a, b)
            },
            |(a, b)| black_box(a).sub(&black_box(b)),
            BatchSize::SmallInput,
        )
    });

    group.bench_function("neg, U256", |b| {
        b.iter_batched(
            || {
                MontyForm::new(
                    &U256::random_mod(&mut OsRng, params.modulus().as_nz_ref()),
                    params,
                )
            },
            |a| black_box(a).neg(),
            BatchSize::SmallInput,
        )
    });

    group.bench_function("invert, U256", |b| {
        b.iter_batched(
            || {
                MontyForm::new(
                    &U256::random_mod(&mut OsRng, params.modulus().as_nz_ref()),
                    params,
                )
            },
            |x| black_box(x).invert(),
            BatchSize::SmallInput,
        )
    });

    group.bench_function("Bernstein-Yang invert, U256", |b| {
        b.iter_batched(
            || {
                let x = MontyForm::new(
                    &U256::random_mod(&mut OsRng, params.modulus().as_nz_ref()),
                    params,
                );
                let inverter = x.params().precompute_inverter();
                (x, inverter)
            },
            |(x, inverter)| inverter.invert(&black_box(x)),
            BatchSize::SmallInput,
        )
    });

    group.bench_function("multiplication, U256*U256", |b| {
        b.iter_batched(
            || {
                let x = MontyForm::new(
                    &U256::random_mod(&mut OsRng, params.modulus().as_nz_ref()),
                    params,
                );
                let y = MontyForm::new(
                    &U256::random_mod(&mut OsRng, params.modulus().as_nz_ref()),
                    params,
                );
                (x, y)
            },
            |(x, y)| black_box(x * y),
            BatchSize::SmallInput,
        )
    });

    group.bench_function("modpow, U256^U256", |b| {
        b.iter_batched(
            || {
                let x = U256::random_mod(&mut OsRng, params.modulus().as_nz_ref());
                let x_m = MontyForm::new(&x, params);
                let p = U256::random_mod(&mut OsRng, params.modulus().as_nz_ref())
                    | (U256::ONE << (U256::BITS - 1));
                (x_m, p)
            },
            |(x, p)| black_box(x.pow(&p)),
            BatchSize::SmallInput,
        )
    });

    #[cfg(feature = "alloc")]
    for i in [1, 2, 3, 4, 10, 100] {
        group.bench_function(
            format!("multi_exponentiate for {i} bases, U256^U256"),
            |b| {
                b.iter_batched(
                    || {
                        let bases_and_exponents: Vec<(MontyForm<{ U256::LIMBS }>, U256)> = (1..=i)
                            .map(|_| {
                                let x = U256::random_mod(&mut OsRng, params.modulus().as_nz_ref());
                                let x_m = MontyForm::new(&x, params);
                                let p = U256::random_mod(&mut OsRng, params.modulus().as_nz_ref())
                                    | (U256::ONE << (U256::BITS - 1));
                                (x_m, p)
                            })
                            .collect();

                        bases_and_exponents
                    },
                    |bases_and_exponents| {
                        black_box(MontyForm::<{ U256::LIMBS }>::multi_exponentiate(
                            bases_and_exponents.as_slice(),
                        ))
                    },
                    BatchSize::SmallInput,
                )
            },
        );
    }
}

fn bench_montgomery(c: &mut Criterion) {
    let mut group = c.benchmark_group("Dynamic Montgomery arithmetic");
    bench_montgomery_conversion(&mut group);
    bench_montgomery_ops(&mut group);
    group.finish();
}

criterion_group!(benches, bench_montgomery);

criterion_main!(benches);
