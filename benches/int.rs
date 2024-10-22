use std::ops::Div;

use criterion::{black_box, criterion_group, criterion_main, BatchSize, Criterion};
use num_traits::WrappingSub;
use rand_core::OsRng;

use crypto_bigint::{NonZero, Random, I1024, I128, I2048, I256, I4096, I512};

fn bench_mul(c: &mut Criterion) {
    let mut group = c.benchmark_group("wrapping ops");

    group.bench_function("split_mul, I128xI128", |b| {
        b.iter_batched(
            || (I256::random(&mut OsRng), I256::random(&mut OsRng)),
            |(x, y)| black_box(x.split_mul(&y)),
            BatchSize::SmallInput,
        )
    });

    group.bench_function("split_mul, I256xI256", |b| {
        b.iter_batched(
            || (I256::random(&mut OsRng), I256::random(&mut OsRng)),
            |(x, y)| black_box(x.split_mul(&y)),
            BatchSize::SmallInput,
        )
    });

    group.bench_function("split_mul, I512xI512", |b| {
        b.iter_batched(
            || (I512::random(&mut OsRng), I512::random(&mut OsRng)),
            |(x, y)| black_box(x.split_mul(&y)),
            BatchSize::SmallInput,
        )
    });

    group.bench_function("split_mul, I1024xI1024", |b| {
        b.iter_batched(
            || (I1024::random(&mut OsRng), I1024::random(&mut OsRng)),
            |(x, y)| black_box(x.split_mul(&y)),
            BatchSize::SmallInput,
        )
    });

    group.bench_function("split_mul, I2048xI2048", |b| {
        b.iter_batched(
            || (I2048::random(&mut OsRng), I2048::random(&mut OsRng)),
            |(x, y)| black_box(x.split_mul(&y)),
            BatchSize::SmallInput,
        )
    });

    group.bench_function("split_mul, I4096xI4096", |b| {
        b.iter_batched(
            || (I4096::random(&mut OsRng), I4096::random(&mut OsRng)),
            |(x, y)| black_box(x.split_mul(&y)),
            BatchSize::SmallInput,
        )
    });
}

fn bench_widening_mul(c: &mut Criterion) {
    let mut group = c.benchmark_group("widening ops");

    group.bench_function("widening_mul, I128xI128", |b| {
        b.iter_batched(
            || (I128::random(&mut OsRng), I128::random(&mut OsRng)),
            |(x, y)| black_box(x.widening_mul(&y)),
            BatchSize::SmallInput,
        )
    });

    group.bench_function("widening_mul, I256xI256", |b| {
        b.iter_batched(
            || (I256::random(&mut OsRng), I256::random(&mut OsRng)),
            |(x, y)| black_box(x.widening_mul(&y)),
            BatchSize::SmallInput,
        )
    });

    group.bench_function("widening_mul, I512xI512", |b| {
        b.iter_batched(
            || (I512::random(&mut OsRng), I512::random(&mut OsRng)),
            |(x, y)| black_box(x.widening_mul(&y)),
            BatchSize::SmallInput,
        )
    });

    group.bench_function("widening_mul, I1024xI1024", |b| {
        b.iter_batched(
            || (I1024::random(&mut OsRng), I1024::random(&mut OsRng)),
            |(x, y)| black_box(x.widening_mul(&y)),
            BatchSize::SmallInput,
        )
    });

    group.bench_function("widening_mul, I2048xI2048", |b| {
        b.iter_batched(
            || (I2048::random(&mut OsRng), I2048::random(&mut OsRng)),
            |(x, y)| black_box(x.widening_mul(&y)),
            BatchSize::SmallInput,
        )
    });

    group.bench_function("widening_mul, I4096xI4096", |b| {
        b.iter_batched(
            || (I4096::random(&mut OsRng), I4096::random(&mut OsRng)),
            |(x, y)| black_box(x.widening_mul(&y)),
            BatchSize::SmallInput,
        )
    });
}

fn bench_div(c: &mut Criterion) {
    let mut group = c.benchmark_group("wrapping ops");

    group.bench_function("div, I256/I128, full size", |b| {
        b.iter_batched(
            || {
                let x = I256::random(&mut OsRng);
                let y = I128::random(&mut OsRng).resize::<{ I256::LIMBS }>();
                (x, NonZero::new(y).unwrap())
            },
            |(x, y)| black_box(x.div(&y)),
            BatchSize::SmallInput,
        )
    });

    group.bench_function("div, I512/I256, full size", |b| {
        b.iter_batched(
            || {
                let x = I512::random(&mut OsRng);
                let y = I256::random(&mut OsRng).resize::<{ I512::LIMBS }>();
                (x, NonZero::new(y).unwrap())
            },
            |(x, y)| black_box(x.div(&y)),
            BatchSize::SmallInput,
        )
    });

    group.bench_function("div, I1024/I512, full size", |b| {
        b.iter_batched(
            || {
                let x = I1024::random(&mut OsRng);
                let y = I512::random(&mut OsRng).resize::<{ I1024::LIMBS }>();
                (x, NonZero::new(y).unwrap())
            },
            |(x, y)| black_box(x.div(&y)),
            BatchSize::SmallInput,
        )
    });

    group.bench_function("div, I2048/I1024, full size", |b| {
        b.iter_batched(
            || {
                let x = I2048::random(&mut OsRng);
                let y = I1024::random(&mut OsRng).resize::<{ I2048::LIMBS }>();
                (x, NonZero::new(y).unwrap())
            },
            |(x, y)| black_box(x.div(&y)),
            BatchSize::SmallInput,
        )
    });

    group.bench_function("div, I4096/I2048, full size", |b| {
        b.iter_batched(
            || {
                let x = I4096::random(&mut OsRng);
                let y = I2048::random(&mut OsRng).resize::<{ I4096::LIMBS }>();
                (x, NonZero::new(y).unwrap())
            },
            |(x, y)| black_box(x.div(&y)),
            BatchSize::SmallInput,
        )
    });

    group.finish();
}

fn bench_add(c: &mut Criterion) {
    let mut group = c.benchmark_group("wrapping ops");

    group.bench_function("add, I128+I128", |b| {
        b.iter_batched(
            || {
                let x = I128::random(&mut OsRng);
                let y = I128::random(&mut OsRng);
                (x, y)
            },
            |(x, y)| black_box(x.wrapping_add(&y)),
            BatchSize::SmallInput,
        )
    });

    group.bench_function("add, I256+I256", |b| {
        b.iter_batched(
            || {
                let x = I256::random(&mut OsRng);
                let y = I256::random(&mut OsRng);
                (x, y)
            },
            |(x, y)| black_box(x.wrapping_add(&y)),
            BatchSize::SmallInput,
        )
    });

    group.bench_function("add, I512+I512", |b| {
        b.iter_batched(
            || {
                let x = I512::random(&mut OsRng);
                let y = I512::random(&mut OsRng);
                (x, y)
            },
            |(x, y)| black_box(x.wrapping_add(&y)),
            BatchSize::SmallInput,
        )
    });

    group.bench_function("add, I1024+I1024", |b| {
        b.iter_batched(
            || {
                let x = I1024::random(&mut OsRng);
                let y = I1024::random(&mut OsRng);
                (x, y)
            },
            |(x, y)| black_box(x.wrapping_add(&y)),
            BatchSize::SmallInput,
        )
    });

    group.bench_function("add, I2048+I2048", |b| {
        b.iter_batched(
            || {
                let x = I2048::random(&mut OsRng);
                let y = I2048::random(&mut OsRng);
                (x, y)
            },
            |(x, y)| black_box(x.wrapping_add(&y)),
            BatchSize::SmallInput,
        )
    });

    group.bench_function("add, I4096+I4096", |b| {
        b.iter_batched(
            || {
                let x = I4096::random(&mut OsRng);
                let y = I4096::random(&mut OsRng);
                (x, y)
            },
            |(x, y)| black_box(x.wrapping_add(&y)),
            BatchSize::SmallInput,
        )
    });

    group.finish();
}

fn bench_sub(c: &mut Criterion) {
    let mut group = c.benchmark_group("wrapping ops");

    group.bench_function("sub, I128-I128", |b| {
        b.iter_batched(
            || {
                let x = I128::random(&mut OsRng);
                let y = I128::random(&mut OsRng);
                (x, y)
            },
            |(x, y)| black_box(x.wrapping_sub(&y)),
            BatchSize::SmallInput,
        )
    });

    group.bench_function("sub, I256-I256", |b| {
        b.iter_batched(
            || {
                let x = I256::random(&mut OsRng);
                let y = I256::random(&mut OsRng);
                (x, y)
            },
            |(x, y)| black_box(x.wrapping_sub(&y)),
            BatchSize::SmallInput,
        )
    });

    group.bench_function("sub, I512-I512", |b| {
        b.iter_batched(
            || {
                let x = I512::random(&mut OsRng);
                let y = I512::random(&mut OsRng);
                (x, y)
            },
            |(x, y)| black_box(x.wrapping_sub(&y)),
            BatchSize::SmallInput,
        )
    });

    group.bench_function("sub, I1024-I1024", |b| {
        b.iter_batched(
            || {
                let x = I1024::random(&mut OsRng);
                let y = I1024::random(&mut OsRng);
                (x, y)
            },
            |(x, y)| black_box(x.wrapping_sub(&y)),
            BatchSize::SmallInput,
        )
    });

    group.bench_function("sub, I2048-I2048", |b| {
        b.iter_batched(
            || {
                let x = I2048::random(&mut OsRng);
                let y = I2048::random(&mut OsRng);
                (x, y)
            },
            |(x, y)| black_box(x.wrapping_sub(&y)),
            BatchSize::SmallInput,
        )
    });

    group.bench_function("sub, I4096-I4096", |b| {
        b.iter_batched(
            || {
                let x = I4096::random(&mut OsRng);
                let y = I4096::random(&mut OsRng);
                (x, y)
            },
            |(x, y)| black_box(x.wrapping_sub(&y)),
            BatchSize::SmallInput,
        )
    });

    group.finish();
}

criterion_group!(
    benches,
    bench_mul,
    bench_widening_mul,
    bench_div,
    bench_add,
    bench_sub,
);

criterion_main!(benches);
