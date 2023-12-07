use criterion::{
    black_box, criterion_group, criterion_main, measurement::Measurement, BatchSize,
    BenchmarkGroup, Criterion,
};
use crypto_bigint::{
    modular::{BoxedResidue, BoxedResidueParams},
    BoxedUint,
};
use rand_core::OsRng;

/// Size of `BoxedUint` to use in benchmark.
const UINT_BITS: u32 = 4096;

fn bench_montgomery_ops<M: Measurement>(group: &mut BenchmarkGroup<'_, M>) {
    let params = BoxedResidueParams::new(
        BoxedUint::random(&mut OsRng, UINT_BITS) | BoxedUint::one_with_precision(UINT_BITS),
    )
    .unwrap();
    group.bench_function("multiplication, BoxedUint*BoxedUint", |b| {
        b.iter_batched(
            || {
                let x = BoxedResidue::new(BoxedUint::random(&mut OsRng, UINT_BITS), params.clone());
                let y = BoxedResidue::new(BoxedUint::random(&mut OsRng, UINT_BITS), params.clone());
                (x, y)
            },
            |(x, y)| black_box(x * y),
            BatchSize::SmallInput,
        )
    });

    let m = BoxedUint::random(&mut OsRng, UINT_BITS) | BoxedUint::one_with_precision(UINT_BITS);
    let params = BoxedResidueParams::new(m).unwrap();
    group.bench_function("modpow, BoxedUint^BoxedUint", |b| {
        b.iter_batched(
            || {
                let x = BoxedUint::random(&mut OsRng, UINT_BITS);
                let x_m = BoxedResidue::new(x, params.clone());
                let p = BoxedUint::random(&mut OsRng, UINT_BITS)
                    | (BoxedUint::one_with_precision(UINT_BITS) << (UINT_BITS - 1));
                (x_m, p)
            },
            |(x, p)| black_box(x.pow(&p)),
            BatchSize::SmallInput,
        )
    });
}

fn bench_montgomery_conversion<M: Measurement>(group: &mut BenchmarkGroup<'_, M>) {
    group.bench_function("BoxedResidueParams creation", |b| {
        b.iter_batched(
            || BoxedUint::random(&mut OsRng, UINT_BITS) | BoxedUint::one_with_precision(UINT_BITS),
            |modulus| BoxedResidueParams::new(modulus),
            BatchSize::SmallInput,
        )
    });

    let params = BoxedResidueParams::new(
        BoxedUint::random(&mut OsRng, UINT_BITS) | BoxedUint::one_with_precision(UINT_BITS),
    )
    .unwrap();
    group.bench_function("BoxedResidue creation", |b| {
        b.iter_batched(
            || BoxedUint::random(&mut OsRng, UINT_BITS),
            |x| black_box(BoxedResidue::new(x, params.clone())),
            BatchSize::SmallInput,
        )
    });

    let params = BoxedResidueParams::new(
        BoxedUint::random(&mut OsRng, UINT_BITS) | BoxedUint::one_with_precision(UINT_BITS),
    )
    .unwrap();
    group.bench_function("BoxedResidue retrieve", |b| {
        b.iter_batched(
            || BoxedResidue::new(BoxedUint::random(&mut OsRng, UINT_BITS), params.clone()),
            |x| black_box(x.retrieve()),
            BatchSize::SmallInput,
        )
    });
}

fn bench_montgomery(c: &mut Criterion) {
    let mut group = c.benchmark_group("Montgomery arithmetic");
    bench_montgomery_conversion(&mut group);
    bench_montgomery_ops(&mut group);
    group.finish();
}

criterion_group!(benches, bench_montgomery);

criterion_main!(benches);
