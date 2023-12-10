use criterion::{
    black_box, criterion_group, criterion_main, measurement::Measurement, BatchSize,
    BenchmarkGroup, Criterion,
};
use crypto_bigint::{Limb, Random};
use rand_core::OsRng;
use subtle::{ConstantTimeEq, ConstantTimeGreater, ConstantTimeLess};

fn bench_cmp<M: Measurement>(group: &mut BenchmarkGroup<'_, M>) {
    group.bench_function("ct_lt", |b| {
        b.iter_batched(
            || {
                let x = Limb::random(&mut OsRng);
                let y = Limb::random(&mut OsRng);
                (x, y)
            },
            |(x, y)| black_box(x.ct_lt(&y)),
            BatchSize::SmallInput,
        )
    });

    group.bench_function("ct_eq", |b| {
        b.iter_batched(
            || {
                let x = Limb::random(&mut OsRng);
                let y = Limb::random(&mut OsRng);
                (x, y)
            },
            |(x, y)| black_box(x.ct_eq(&y)),
            BatchSize::SmallInput,
        )
    });

    group.bench_function("ct_gt", |b| {
        b.iter_batched(
            || {
                let x = Limb::random(&mut OsRng);
                let y = Limb::random(&mut OsRng);
                (x, y)
            },
            |(x, y)| black_box(x.ct_gt(&y)),
            BatchSize::SmallInput,
        )
    });
}

fn bench_ops(c: &mut Criterion) {
    let mut group = c.benchmark_group("ops");
    bench_cmp(&mut group);
    group.finish();
}

criterion_group!(benches, bench_ops);

criterion_main!(benches);
