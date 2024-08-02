use criterion::{black_box, criterion_group, criterion_main, BatchSize, Criterion};
use crypto_bigint::{BoxedUint, Limb, NonZero, RandomBits};
use rand_core::OsRng;

/// Size of `BoxedUint` to use in benchmark.
const UINT_BITS: u32 = 4096;

fn bench_shifts(c: &mut Criterion) {
    let mut group = c.benchmark_group("bit shifts");

    group.bench_function("shl_vartime", |b| {
        b.iter_batched(
            || BoxedUint::random_bits(&mut OsRng, UINT_BITS),
            |x| black_box(x.shl_vartime(UINT_BITS / 2 + 10)),
            BatchSize::SmallInput,
        )
    });

    group.bench_function("shl", |b| {
        b.iter_batched(
            || BoxedUint::random_bits(&mut OsRng, UINT_BITS),
            |x| x.overflowing_shl(UINT_BITS / 2 + 10),
            BatchSize::SmallInput,
        )
    });

    group.bench_function("shr_vartime", |b| {
        b.iter_batched(
            || BoxedUint::random_bits(&mut OsRng, UINT_BITS),
            |x| black_box(x.shr_vartime(UINT_BITS / 2 + 10)),
            BatchSize::SmallInput,
        )
    });

    group.bench_function("shr", |b| {
        b.iter_batched(
            || BoxedUint::random_bits(&mut OsRng, UINT_BITS),
            |x| x.overflowing_shr(UINT_BITS / 2 + 10),
            BatchSize::SmallInput,
        )
    });

    group.finish();
}

fn bench_division(c: &mut Criterion) {
    let mut group = c.benchmark_group("wrapping ops");

    group.bench_function("boxed_div_rem", |b| {
        b.iter_batched(
            || {
                (
                    BoxedUint::max(UINT_BITS),
                    NonZero::new(BoxedUint::random_bits_with_precision(
                        &mut OsRng,
                        UINT_BITS / 2,
                        UINT_BITS,
                    ))
                    .unwrap(),
                )
            },
            |(x, y)| black_box(x.div_rem(&y)),
            BatchSize::SmallInput,
        )
    });

    group.bench_function("boxed_div_rem_vartime", |b| {
        b.iter_batched(
            || {
                (
                    BoxedUint::max(UINT_BITS),
                    NonZero::new(BoxedUint::random_bits_with_precision(
                        &mut OsRng,
                        UINT_BITS / 2,
                        UINT_BITS,
                    ))
                    .unwrap(),
                )
            },
            |(x, y)| black_box(x.div_rem_vartime(&y)),
            BatchSize::SmallInput,
        )
    });

    group.bench_function("boxed_div_rem_limb", |b| {
        b.iter_batched(
            || (BoxedUint::max(UINT_BITS), NonZero::new(Limb::ONE).unwrap()),
            |(x, y)| black_box(x.div_rem_limb(y)),
            BatchSize::SmallInput,
        )
    });

    group.bench_function("boxed_rem", |b| {
        b.iter_batched(
            || {
                (
                    BoxedUint::max(UINT_BITS),
                    NonZero::new(BoxedUint::random_bits_with_precision(
                        &mut OsRng,
                        UINT_BITS / 2,
                        UINT_BITS,
                    ))
                    .unwrap(),
                )
            },
            |(x, y)| black_box(x.rem(&y)),
            BatchSize::SmallInput,
        )
    });

    group.bench_function("boxed_rem_vartime", |b| {
        b.iter_batched(
            || {
                (
                    BoxedUint::max(UINT_BITS),
                    NonZero::new(BoxedUint::random_bits_with_precision(
                        &mut OsRng,
                        UINT_BITS / 2,
                        UINT_BITS,
                    ))
                    .unwrap(),
                )
            },
            |(x, y)| black_box(x.rem_vartime(&y)),
            BatchSize::SmallInput,
        )
    });

    group.bench_function("boxed_rem_limb", |b| {
        b.iter_batched(
            || (BoxedUint::max(UINT_BITS), NonZero::new(Limb::ONE).unwrap()),
            |(x, y)| black_box(x.rem_limb(y)),
            BatchSize::SmallInput,
        )
    });

    group.finish();
}

fn bench_boxed_sqrt(c: &mut Criterion) {
    let mut group = c.benchmark_group("boxed_sqrt");
    group.bench_function("boxed_sqrt, 4096", |b| {
        b.iter_batched(
            || BoxedUint::random_bits(&mut OsRng, UINT_BITS),
            |x| x.sqrt(),
            BatchSize::SmallInput,
        )
    });

    group.bench_function("boxed_sqrt_vartime, 4096", |b| {
        b.iter_batched(
            || BoxedUint::random_bits(&mut OsRng, UINT_BITS),
            |x| x.sqrt_vartime(),
            BatchSize::SmallInput,
        )
    });
}

criterion_group!(benches, bench_division, bench_shifts, bench_boxed_sqrt);

criterion_main!(benches);
