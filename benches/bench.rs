use criterion::{
    criterion_group, criterion_main, measurement::Measurement, BatchSize, BenchmarkGroup, Criterion,
};
use crypto_bigint::{
    modular::runtime_mod::{DynResidue, DynResidueParams},
    Limb, NonZero, Random, Reciprocal, U128, U4096,
};
use rand_core::OsRng;

// fn bench_division<M: Measurement>(group: &mut BenchmarkGroup<'_, M>) {
//     group.bench_function("div/rem, U4096/U128, full size", |b| {
//         b.iter_batched(
//             || {
//                 let x = U4096::random(&mut OsRng);
//                 let y_half = U128::random(&mut OsRng);
//                 let y: U4096 = (y_half, U128::ZERO).into();
//                 (x, NonZero::new(y).unwrap())
//             },
//             |(x, y)| x.div_rem(&y),
//             BatchSize::SmallInput,
//         )
//     });
//
//     group.bench_function("rem, U4096/U128, full size", |b| {
//         b.iter_batched(
//             || {
//                 let x = U4096::random(&mut OsRng);
//                 let y_half = U128::random(&mut OsRng);
//                 let y: U4096 = (y_half, U128::ZERO).into();
//                 (x, NonZero::new(y).unwrap())
//             },
//             |(x, y)| x.rem(&y),
//             BatchSize::SmallInput,
//         )
//     });
//
//     group.bench_function("div/rem, U4096/Limb, full size", |b| {
//         b.iter_batched(
//             || {
//                 let x = U4096::random(&mut OsRng);
//                 let y_small = Limb::random(&mut OsRng);
//                 let y = U4096::from_word(y_small.0);
//                 (x, NonZero::new(y).unwrap())
//             },
//             |(x, y)| x.div_rem(&y),
//             BatchSize::SmallInput,
//         )
//     });
//
//     group.bench_function("div/rem, U4096/Limb, single limb", |b| {
//         b.iter_batched(
//             || {
//                 let x = U4096::random(&mut OsRng);
//                 let y = Limb::random(&mut OsRng);
//                 (x, NonZero::new(y).unwrap())
//             },
//             |(x, y)| x.div_rem_limb(y),
//             BatchSize::SmallInput,
//         )
//     });
//
//     group.bench_function("div/rem, U4096/Limb, single limb with reciprocal", |b| {
//         b.iter_batched(
//             || {
//                 let x = U4096::random(&mut OsRng);
//                 let y = Limb::random(&mut OsRng);
//                 let r = Reciprocal::new(y);
//                 (x, r)
//             },
//             |(x, r)| x.div_rem_limb_with_reciprocal(&r),
//             BatchSize::SmallInput,
//         )
//     });
// }

fn bench_montgomery_ops<M: Measurement>(group: &mut BenchmarkGroup<'_, M>) {
    let params = DynResidueParams::new(&(U4096::random(&mut OsRng) | U4096::ONE));
    group.bench_function("multiplication, U4096*U4096", |b| {
        b.iter_batched(
            || {
                let x = DynResidue::new(&U4096::random(&mut OsRng), params);
                let y = DynResidue::new(&U4096::random(&mut OsRng), params);
                (x, y)
            },
            |(x, y)| x * y,
            BatchSize::SmallInput,
        )
    });

    let m = U4096::random(&mut OsRng) | U4096::ONE;
    let params = DynResidueParams::new(&m);
    group.bench_function("modpow, U4096^U4096", |b| {
        b.iter_batched(
            || {
                let x = U4096::random(&mut OsRng);
                let x_m = DynResidue::new(&x, params);
                let p = U4096::random(&mut OsRng) | (U4096::ONE << (U4096::BITS - 1));
                (x_m, p)
            },
            |(x, p)| x.pow(&p),
            BatchSize::SmallInput,
        )
    });

    for i in [1, 2, 3, 4, 10, 100] {
        group.bench_function(
            format!("multi_exponentiate for {i} bases, U4096^U4096"),
            |b| {
                b.iter_batched(
                    || {
                        let bases_and_exponents: Vec<(DynResidue<{ U4096::LIMBS }>, U4096)> = (1
                            ..=i)
                            .map(|_| {
                                let x = U4096::random(&mut OsRng);
                                let x_m = DynResidue::new(&x, params);
                                let p =
                                    U4096::random(&mut OsRng) | (U4096::ONE << (U4096::BITS - 1));
                                (x_m, p)
                            })
                            .collect();

                        bases_and_exponents
                    },
                    |bases_and_exponents| {
                        DynResidue::<{ U4096::LIMBS }>::multi_exponentiate(
                            bases_and_exponents,
                            params,
                        )
                    },
                    BatchSize::SmallInput,
                )
            },
        );
    }
}

fn bench_montgomery_conversion<M: Measurement>(group: &mut BenchmarkGroup<'_, M>) {
    group.bench_function("DynResidueParams creation", |b| {
        b.iter_batched(
            || U4096::random(&mut OsRng) | U4096::ONE,
            |modulus| DynResidueParams::new(&modulus),
            BatchSize::SmallInput,
        )
    });

    let params = DynResidueParams::new(&(U4096::random(&mut OsRng) | U4096::ONE));
    group.bench_function("DynResidue creation", |b| {
        b.iter_batched(
            || U4096::random(&mut OsRng),
            |x| DynResidue::new(&x, params),
            BatchSize::SmallInput,
        )
    });

    let params = DynResidueParams::new(&(U4096::random(&mut OsRng) | U4096::ONE));
    group.bench_function("DynResidue retrieve", |b| {
        b.iter_batched(
            || DynResidue::new(&U4096::random(&mut OsRng), params),
            |x| x.retrieve(),
            BatchSize::SmallInput,
        )
    });
}

// fn bench_wrapping_ops(c: &mut Criterion) {
//     let mut group = c.benchmark_group("wrapping ops");
//     bench_division(&mut group);
//     group.finish();
// }

fn bench_montgomery(c: &mut Criterion) {
    let mut group = c.benchmark_group("Montgomery arithmetic");
    // bench_montgomery_conversion(&mut group);
    bench_montgomery_ops(&mut group);
    group.finish();
}

criterion_group!(benches, bench_montgomery);
criterion_main!(benches);
