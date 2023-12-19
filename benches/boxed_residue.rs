use criterion::{
    black_box, criterion_group, criterion_main, measurement::Measurement, BatchSize,
    BenchmarkGroup, Criterion,
};
use crypto_bigint::{
    modular::{BoxedResidue, BoxedResidueParams},
    BoxedUint, NonZero, RandomMod,
};
use num_bigint::BigUint;
use rand_core::OsRng;

/// Size of `BoxedUint` to use in benchmark.
const UINT_BITS: u32 = 4096;

fn to_biguint(uint: &BoxedUint) -> BigUint {
    BigUint::from_bytes_be(&uint.to_be_bytes())
}

fn bench_montgomery_ops<M: Measurement>(group: &mut BenchmarkGroup<'_, M>) {
    let params = BoxedResidueParams::new(
        BoxedUint::random(&mut OsRng, UINT_BITS) | BoxedUint::one_with_precision(UINT_BITS),
    )
    .unwrap();

    group.bench_function("invert, U256", |b| {
        b.iter_batched(
            || {
                let modulus = NonZero::new(params.modulus().clone()).unwrap();
                BoxedResidue::new(BoxedUint::random_mod(&mut OsRng, &modulus), params.clone())
            },
            |x| black_box(x).invert(),
            BatchSize::SmallInput,
        )
    });

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

    let modulus = to_biguint(params.modulus());
    group.bench_function("multiplication, BigUint*BigUint (num-bigint-dig)", |b| {
        b.iter_batched(
            || {
                let x = to_biguint(&BoxedUint::random(&mut OsRng, UINT_BITS)) % &modulus;
                let y = to_biguint(&BoxedUint::random(&mut OsRng, UINT_BITS)) % &modulus;
                (x, y)
            },
            |(x, y)| x * y % &modulus,
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

    group.bench_function("modpow, BigUint^BigUint (num-bigint-dig)", |b| {
        b.iter_batched(
            || {
                let x = to_biguint(&BoxedUint::random(&mut OsRng, UINT_BITS));
                let x_m = x % &modulus;
                let p = to_biguint(
                    &(BoxedUint::random(&mut OsRng, UINT_BITS)
                        | (BoxedUint::one_with_precision(UINT_BITS) << (UINT_BITS - 1))),
                );
                (x_m, p)
            },
            |(x, p)| black_box(x.modpow(&p, &modulus)),
            BatchSize::SmallInput,
        )
    });
}

fn bench_montgomery_conversion<M: Measurement>(group: &mut BenchmarkGroup<'_, M>) {
    group.bench_function("BoxedResidueParams::new", |b| {
        b.iter_batched(
            || BoxedUint::random(&mut OsRng, UINT_BITS) | BoxedUint::one_with_precision(UINT_BITS),
            |modulus| black_box(BoxedResidueParams::new(modulus)),
            BatchSize::SmallInput,
        )
    });

    group.bench_function("BoxedResidueParams::new_vartime", |b| {
        b.iter_batched(
            || BoxedUint::random(&mut OsRng, UINT_BITS) | BoxedUint::one_with_precision(UINT_BITS),
            |modulus| black_box(BoxedResidueParams::new_vartime(modulus)),
            BatchSize::SmallInput,
        )
    });

    let params = BoxedResidueParams::new(
        BoxedUint::random(&mut OsRng, UINT_BITS) | BoxedUint::one_with_precision(UINT_BITS),
    )
    .unwrap();
    group.bench_function("BoxedResidue::new", |b| {
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
    group.bench_function("BoxedResidue::retrieve", |b| {
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
