use criterion::{
    black_box, criterion_group, criterion_main, measurement::Measurement, BatchSize,
    BenchmarkGroup, Criterion,
};
use crypto_bigint::{Limb, NonZero, Random, Reciprocal, U128, U2048, U256};
use rand_core::OsRng;

fn bench_division<M: Measurement>(group: &mut BenchmarkGroup<'_, M>) {
    group.bench_function("div/rem, U256/U128, full size", |b| {
        b.iter_batched(
            || {
                let x = U256::random(&mut OsRng);
                let y_half = U128::random(&mut OsRng);
                let y: U256 = (y_half, U128::ZERO).into();
                (x, NonZero::new(y).unwrap())
            },
            |(x, y)| black_box(x.div_rem(&y)),
            BatchSize::SmallInput,
        )
    });

    group.bench_function("rem, U256/U128, full size", |b| {
        b.iter_batched(
            || {
                let x = U256::random(&mut OsRng);
                let y_half = U128::random(&mut OsRng);
                let y: U256 = (y_half, U128::ZERO).into();
                (x, NonZero::new(y).unwrap())
            },
            |(x, y)| black_box(x.rem(&y)),
            BatchSize::SmallInput,
        )
    });

    group.bench_function("div/rem, U256/Limb, full size", |b| {
        b.iter_batched(
            || {
                let x = U256::random(&mut OsRng);
                let y_small = Limb::random(&mut OsRng);
                let y = U256::from_word(y_small.0);
                (x, NonZero::new(y).unwrap())
            },
            |(x, y)| black_box(x.div_rem(&y)),
            BatchSize::SmallInput,
        )
    });

    group.bench_function("div/rem, U256/Limb, single limb", |b| {
        b.iter_batched(
            || {
                let x = U256::random(&mut OsRng);
                let y = Limb::random(&mut OsRng);
                (x, NonZero::new(y).unwrap())
            },
            |(x, y)| black_box(x.div_rem_limb(y)),
            BatchSize::SmallInput,
        )
    });

    group.bench_function("div/rem, U256/Limb, single limb with reciprocal", |b| {
        b.iter_batched(
            || {
                let x = U256::random(&mut OsRng);
                let y = Limb::random(&mut OsRng);
                let r = Reciprocal::new(y);
                (x, r)
            },
            |(x, r)| black_box(x.div_rem_limb_with_reciprocal(&r)),
            BatchSize::SmallInput,
        )
    });
}

fn bench_shifts<M: Measurement>(group: &mut BenchmarkGroup<'_, M>) {
    group.bench_function("shl_vartime, small, U2048", |b| {
        b.iter_batched(|| U2048::ONE, |x| x.shl_vartime(10), BatchSize::SmallInput)
    });

    group.bench_function("shl_vartime, large, U2048", |b| {
        b.iter_batched(
            || U2048::ONE,
            |x| black_box(x.shl_vartime(1024 + 10)),
            BatchSize::SmallInput,
        )
    });

    group.bench_function("shl, U2048", |b| {
        b.iter_batched(|| U2048::ONE, |x| x.shl(1024 + 10), BatchSize::SmallInput)
    });

    group.bench_function("shr, U2048", |b| {
        b.iter_batched(|| U2048::ONE, |x| x.shr(1024 + 10), BatchSize::SmallInput)
    });
}

fn bench_inv_mod<M: Measurement>(group: &mut BenchmarkGroup<'_, M>) {
    group.bench_function("inv_odd_mod, U256", |b| {
        b.iter_batched(
            || {
                let m = U256::random(&mut OsRng) | U256::ONE;
                loop {
                    let x = U256::random(&mut OsRng);
                    let (_, is_some) = x.inv_odd_mod(&m);
                    if is_some.into() {
                        break (x, m);
                    }
                }
            },
            |(x, m)| black_box(x.inv_odd_mod(&m)),
            BatchSize::SmallInput,
        )
    });

    group.bench_function("inv_mod, U256, odd modulus", |b| {
        b.iter_batched(
            || {
                let m = U256::random(&mut OsRng) | U256::ONE;
                loop {
                    let x = U256::random(&mut OsRng);
                    let (_, is_some) = x.inv_odd_mod(&m);
                    if is_some.into() {
                        break (x, m);
                    }
                }
            },
            |(x, m)| black_box(x.inv_mod(&m)),
            BatchSize::SmallInput,
        )
    });

    group.bench_function("inv_mod, U256", |b| {
        b.iter_batched(
            || {
                let m = U256::random(&mut OsRng);
                loop {
                    let x = U256::random(&mut OsRng);
                    let (_, is_some) = black_box(x.inv_mod(&m));
                    if is_some.into() {
                        break (x, m);
                    }
                }
            },
            |(x, m)| black_box(x.inv_mod(&m)),
            BatchSize::SmallInput,
        )
    });
}

fn bench_wrapping_ops(c: &mut Criterion) {
    let mut group = c.benchmark_group("wrapping ops");
    bench_division(&mut group);
    group.finish();
}

fn bench_modular_ops(c: &mut Criterion) {
    let mut group = c.benchmark_group("modular ops");
    bench_shifts(&mut group);
    bench_inv_mod(&mut group);
    group.finish();
}

criterion_group!(benches, bench_wrapping_ops, bench_modular_ops);

criterion_main!(benches);
