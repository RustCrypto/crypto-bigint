use criterion::{black_box, criterion_group, criterion_main, BatchSize, Criterion};
use crypto_bigint::{BoxedUint, Limb, NonZero, RandomBits};
use num_bigint::BigUint;
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
            |x| black_box(x.overflowing_shl(UINT_BITS / 2 + 10)),
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
            |x| black_box(x.overflowing_shr(UINT_BITS / 2 + 10)),
            BatchSize::SmallInput,
        )
    });

    group.finish();
}

fn bench_mul(c: &mut Criterion) {
    let mut group = c.benchmark_group("wrapping ops");

    group.bench_function("boxed_mul", |b| {
        b.iter_batched(
            || {
                (
                    BoxedUint::random_bits(&mut OsRng, UINT_BITS),
                    BoxedUint::random_bits(&mut OsRng, UINT_BITS),
                )
            },
            |(x, y)| black_box(x.mul(&y)),
            BatchSize::SmallInput,
        )
    });

    group.bench_function("boxed_square", |b| {
        b.iter_batched(
            || BoxedUint::random_bits(&mut OsRng, UINT_BITS),
            |x| black_box(x.square()),
            BatchSize::SmallInput,
        )
    });
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
            |x| black_box(x.sqrt()),
            BatchSize::SmallInput,
        )
    });

    group.bench_function("boxed_sqrt_vartime, 4096", |b| {
        b.iter_batched(
            || BoxedUint::random_bits(&mut OsRng, UINT_BITS),
            |x| black_box(x.sqrt_vartime()),
            BatchSize::SmallInput,
        )
    });
}

fn bench_radix_encoding(c: &mut Criterion) {
    let mut group = c.benchmark_group("boxed_radix_encode");

    for radix in [2, 8, 10] {
        group.bench_function(format!("from_str_radix_vartime, {radix}"), |b| {
            b.iter_batched(
                || BoxedUint::random_bits(&mut OsRng, UINT_BITS).to_string_radix_vartime(10),
                |x| {
                    black_box(BoxedUint::from_str_radix_with_precision_vartime(
                        &x, radix, UINT_BITS,
                    ))
                },
                BatchSize::SmallInput,
            )
        });

        group.bench_function(format!("parse_bytes, {radix} (num-bigint-dig)"), |b| {
            b.iter_batched(
                || BoxedUint::random_bits(&mut OsRng, UINT_BITS).to_string_radix_vartime(10),
                |x| black_box(BigUint::parse_bytes(x.as_bytes(), radix)),
                BatchSize::SmallInput,
            )
        });

        group.bench_function(format!("to_str_radix_vartime, {radix}"), |b| {
            b.iter_batched(
                || BoxedUint::random_bits(&mut OsRng, UINT_BITS),
                |x| black_box(x.to_string_radix_vartime(radix)),
                BatchSize::SmallInput,
            )
        });

        group.bench_function(format!("to_str_radix, {radix} (num-bigint-dig)"), |b| {
            b.iter_batched(
                || {
                    let u = BoxedUint::random_bits(&mut OsRng, UINT_BITS);
                    BigUint::from_bytes_be(&u.to_be_bytes())
                },
                |x| black_box(x.to_str_radix(radix)),
                BatchSize::SmallInput,
            )
        });
    }
}

criterion_group!(
    benches,
    bench_mul,
    bench_division,
    bench_shifts,
    bench_boxed_sqrt,
    bench_radix_encoding,
);

criterion_main!(benches);
