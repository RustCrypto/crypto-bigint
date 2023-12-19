use criterion::{
    black_box, criterion_group, criterion_main, measurement::Measurement, BatchSize,
    BenchmarkGroup, Criterion,
};
use crypto_bigint::{
    modular::{DynResidue, DynResidueParams},
    Invert, Inverter, PrecomputeInverter, Random, U256,
};
use rand_core::OsRng;

#[cfg(feature = "alloc")]
use crypto_bigint::MultiExponentiate;

fn bench_montgomery_conversion<M: Measurement>(group: &mut BenchmarkGroup<'_, M>) {
    group.bench_function("DynResidueParams creation", |b| {
        b.iter_batched(
            || U256::random(&mut OsRng) | U256::ONE,
            |modulus| black_box(DynResidueParams::new(&modulus)),
            BatchSize::SmallInput,
        )
    });

    let params = DynResidueParams::new(&(U256::random(&mut OsRng) | U256::ONE)).unwrap();
    group.bench_function("DynResidue creation", |b| {
        b.iter_batched(
            || U256::random(&mut OsRng),
            |x| black_box(DynResidue::new(&x, params)),
            BatchSize::SmallInput,
        )
    });

    let params = DynResidueParams::new(&(U256::random(&mut OsRng) | U256::ONE)).unwrap();
    group.bench_function("DynResidue retrieve", |b| {
        b.iter_batched(
            || DynResidue::new(&U256::random(&mut OsRng), params),
            |x| black_box(x.retrieve()),
            BatchSize::SmallInput,
        )
    });
}

fn bench_montgomery_ops<M: Measurement>(group: &mut BenchmarkGroup<'_, M>) {
    let params = DynResidueParams::new(&(U256::random(&mut OsRng) | U256::ONE)).unwrap();

    group.bench_function("invert, U256", |b| {
        b.iter_batched(
            || DynResidue::new(&U256::random(&mut OsRng), params),
            |x| black_box(x).invert(),
            BatchSize::SmallInput,
        )
    });

    group.bench_function("Bernstein-Yang invert, U256", |b| {
        b.iter_batched(
            || {
                let x = DynResidue::new(&U256::random(&mut OsRng), params);
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
                let x = DynResidue::new(&U256::random(&mut OsRng), params);
                let y = DynResidue::new(&U256::random(&mut OsRng), params);
                (x, y)
            },
            |(x, y)| black_box(x * y),
            BatchSize::SmallInput,
        )
    });

    group.bench_function("modpow, U256^U256", |b| {
        b.iter_batched(
            || {
                let x = U256::random(&mut OsRng);
                let x_m = DynResidue::new(&x, params);
                let p = U256::random(&mut OsRng) | (U256::ONE << (U256::BITS - 1));
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
                        let bases_and_exponents: Vec<(DynResidue<{ U256::LIMBS }>, U256)> = (1..=i)
                            .map(|_| {
                                let x = U256::random(&mut OsRng);
                                let x_m = DynResidue::new(&x, params);
                                let p = U256::random(&mut OsRng) | (U256::ONE << (U256::BITS - 1));
                                (x_m, p)
                            })
                            .collect();

                        bases_and_exponents
                    },
                    |bases_and_exponents| {
                        black_box(DynResidue::<{ U256::LIMBS }>::multi_exponentiate(
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
    let mut group = c.benchmark_group("Montgomery arithmetic");
    bench_montgomery_conversion(&mut group);
    bench_montgomery_ops(&mut group);
    group.finish();
}

criterion_group!(benches, bench_montgomery);

criterion_main!(benches);
