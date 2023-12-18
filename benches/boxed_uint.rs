use criterion::{black_box, criterion_group, criterion_main, BatchSize, Criterion};
use crypto_bigint::BoxedUint;
use rand_core::OsRng;

/// Size of `BoxedUint` to use in benchmark.
const UINT_BITS: u32 = 4096;

fn bench_shifts(c: &mut Criterion) {
    let mut group = c.benchmark_group("bit shifts");

    group.bench_function("shl_vartime", |b| {
        b.iter_batched(
            || BoxedUint::random(&mut OsRng, UINT_BITS),
            |x| black_box(x.overflowing_shl(UINT_BITS / 2 + 10).0),
            BatchSize::SmallInput,
        )
    });

    group.bench_function("shl", |b| {
        b.iter_batched(
            || BoxedUint::random(&mut OsRng, UINT_BITS),
            |x| x.overflowing_shl(UINT_BITS / 2 + 10),
            BatchSize::SmallInput,
        )
    });

    group.bench_function("shr_vartime", |b| {
        b.iter_batched(
            || BoxedUint::random(&mut OsRng, UINT_BITS),
            |x| black_box(x.overflowing_shr(UINT_BITS / 2 + 10).0),
            BatchSize::SmallInput,
        )
    });

    group.bench_function("shr", |b| {
        b.iter_batched(
            || BoxedUint::random(&mut OsRng, UINT_BITS),
            |x| x.overflowing_shr(UINT_BITS / 2 + 10),
            BatchSize::SmallInput,
        )
    });

    group.finish();
}

criterion_group!(benches, bench_shifts);

criterion_main!(benches);
