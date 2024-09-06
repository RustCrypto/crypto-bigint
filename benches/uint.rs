use criterion::{black_box, criterion_group, criterion_main, BatchSize, Criterion};
use crypto_bigint::{
    Limb, NonZero, Odd, Random, RandomMod, Reciprocal, Uint, U128, U2048, U256, U4096,
};
use rand_core::OsRng;

fn bench_mul(c: &mut Criterion) {
    let mut group = c.benchmark_group("wrapping ops");

    group.bench_function("split_mul, U256xU256", |b| {
        b.iter_batched(
            || (U256::random(&mut OsRng), U256::random(&mut OsRng)),
            |(x, y)| black_box(x.split_mul(&y)),
            BatchSize::SmallInput,
        )
    });

    group.bench_function("split_mul, U4096xU4096", |b| {
        b.iter_batched(
            || (U4096::random(&mut OsRng), U4096::random(&mut OsRng)),
            |(x, y)| black_box(x.split_mul(&y)),
            BatchSize::SmallInput,
        )
    });

    group.bench_function("square_wide, U256", |b| {
        b.iter_batched(
            || U256::random(&mut OsRng),
            |x| black_box(x.square_wide()),
            BatchSize::SmallInput,
        )
    });

    group.bench_function("square_wide, U4096", |b| {
        b.iter_batched(
            || U4096::random(&mut OsRng),
            |x| black_box(x.square_wide()),
            BatchSize::SmallInput,
        )
    });

    group.bench_function("mul_mod, U256", |b| {
        b.iter_batched(
            || {
                let m = Odd::<U256>::random(&mut OsRng);
                let x = U256::random_mod(&mut OsRng, m.as_nz_ref());
                (m.to_nz().unwrap(), x)
            },
            |(m, x)| black_box(x).mul_mod(black_box(&x), &m),
            BatchSize::SmallInput,
        )
    });

    group.bench_function("mul_mod_vartime, U256", |b| {
        b.iter_batched(
            || {
                let m = Odd::<U256>::random(&mut OsRng);
                let x = U256::random_mod(&mut OsRng, m.as_nz_ref());
                (m.to_nz().unwrap(), x)
            },
            |(m, x)| black_box(x).mul_mod_vartime(black_box(&x), &m),
            BatchSize::SmallInput,
        )
    });

    group.bench_function("mul_mod_special, U256", |b| {
        b.iter_batched(
            || {
                let m = Limb::random(&mut OsRng);
                let x = U256::random(&mut OsRng);
                (m, x)
            },
            |(m, x)| black_box(x).mul_mod_special(black_box(&x), m),
            BatchSize::SmallInput,
        )
    });
}

fn bench_division(c: &mut Criterion) {
    let mut group = c.benchmark_group("wrapping ops");

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

    group.bench_function("div/rem_vartime, U256/U128, full size", |b| {
        b.iter_batched(
            || {
                let x = U256::random(&mut OsRng);
                let y: U256 = (U128::MAX, U128::ZERO).into();
                (x, NonZero::new(y).unwrap())
            },
            |(x, y)| black_box(x.div_rem_vartime(&y)),
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

    group.bench_function("rem_vartime, U256/U128, full size", |b| {
        b.iter_batched(
            || {
                let x = U256::random(&mut OsRng);
                let y: U256 = (U128::MAX, U128::ZERO).into();
                (x, NonZero::new(y).unwrap())
            },
            |(x, y)| black_box(x.rem_vartime(&y)),
            BatchSize::SmallInput,
        )
    });

    group.bench_function("rem_wide_vartime, U256", |b| {
        b.iter_batched(
            || {
                let (x_lo, x_hi) = (U256::random(&mut OsRng), U256::random(&mut OsRng));
                let y: U256 = (U128::MAX, U128::ZERO).into();
                (x_lo, x_hi, NonZero::new(y).unwrap())
            },
            |(x_lo, x_hi, y)| black_box(Uint::rem_wide_vartime((x_lo, x_hi), &y)),
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
                let mut y = Limb::random(&mut OsRng);
                if y == Limb::ZERO {
                    y = Limb::ONE;
                }
                let r = Reciprocal::new(NonZero::new(y).unwrap());
                (x, r)
            },
            |(x, r)| black_box(x.div_rem_limb_with_reciprocal(&r)),
            BatchSize::SmallInput,
        )
    });

    group.finish();
}

fn bench_gcd(c: &mut Criterion) {
    let mut group = c.benchmark_group("greatest common divisor");

    group.bench_function("gcd, U256", |b| {
        b.iter_batched(
            || {
                let f = U256::random(&mut OsRng);
                let g = U256::random(&mut OsRng);
                (f, g)
            },
            |(f, g)| black_box(f.gcd(&g)),
            BatchSize::SmallInput,
        )
    });

    group.bench_function("gcd_vartime, U256", |b| {
        b.iter_batched(
            || {
                let f = Odd::<U256>::random(&mut OsRng);
                let g = U256::random(&mut OsRng);
                (f, g)
            },
            |(f, g)| black_box(f.gcd_vartime(&g)),
            BatchSize::SmallInput,
        )
    });

    group.finish();
}

fn bench_shl(c: &mut Criterion) {
    let mut group = c.benchmark_group("left shift");

    group.bench_function("shl_vartime, small, U2048", |b| {
        b.iter_batched(
            || U2048::ONE,
            |x| x.overflowing_shl_vartime(10),
            BatchSize::SmallInput,
        )
    });

    group.bench_function("shl_vartime, large, U2048", |b| {
        b.iter_batched(
            || U2048::ONE,
            |x| black_box(x.overflowing_shl_vartime(1024 + 10)),
            BatchSize::SmallInput,
        )
    });

    group.bench_function("shl_vartime_wide, large, U2048", |b| {
        b.iter_batched(
            || (U2048::ONE, U2048::ONE),
            |x| Uint::overflowing_shl_vartime_wide(x, 1024 + 10),
            BatchSize::SmallInput,
        )
    });

    group.bench_function("shl, U2048", |b| {
        b.iter_batched(
            || U2048::ONE,
            |x| x.overflowing_shl(1024 + 10),
            BatchSize::SmallInput,
        )
    });

    group.finish();
}

fn bench_shr(c: &mut Criterion) {
    let mut group = c.benchmark_group("right shift");

    group.bench_function("shr_vartime, small, U2048", |b| {
        b.iter_batched(
            || U2048::ONE,
            |x| x.overflowing_shr_vartime(10),
            BatchSize::SmallInput,
        )
    });

    group.bench_function("shr_vartime, large, U2048", |b| {
        b.iter_batched(
            || U2048::ONE,
            |x| x.overflowing_shr_vartime(1024 + 10),
            BatchSize::SmallInput,
        )
    });

    group.bench_function("shr_vartime_wide, large, U2048", |b| {
        b.iter_batched(
            || (U2048::ONE, U2048::ONE),
            |x| Uint::overflowing_shr_vartime_wide(x, 1024 + 10),
            BatchSize::SmallInput,
        )
    });

    group.bench_function("shr, U2048", |b| {
        b.iter_batched(
            || U2048::ONE,
            |x| x.overflowing_shr(1024 + 10),
            BatchSize::SmallInput,
        )
    });

    group.finish();
}

fn bench_inv_mod(c: &mut Criterion) {
    let mut group = c.benchmark_group("modular ops");

    group.bench_function("inv_odd_mod, U256", |b| {
        b.iter_batched(
            || {
                let m = Odd::<U256>::random(&mut OsRng);
                loop {
                    let x = U256::random(&mut OsRng);
                    let inv_x = x.inv_odd_mod(&m);
                    if inv_x.is_some().into() {
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
                let m = Odd::<U256>::random(&mut OsRng);
                loop {
                    let x = U256::random(&mut OsRng);
                    let inv_x = x.inv_odd_mod(&m);
                    if inv_x.is_some().into() {
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
                    let inv_x = x.inv_mod(&m);
                    if inv_x.is_some().into() {
                        break (x, m);
                    }
                }
            },
            |(x, m)| black_box(x.inv_mod(&m)),
            BatchSize::SmallInput,
        )
    });

    group.finish();
}

fn bench_sqrt(c: &mut Criterion) {
    let mut group = c.benchmark_group("sqrt");

    group.bench_function("sqrt, U256", |b| {
        b.iter_batched(
            || U256::random(&mut OsRng),
            |x| x.sqrt(),
            BatchSize::SmallInput,
        )
    });

    group.bench_function("sqrt_vartime, U256", |b| {
        b.iter_batched(
            || U256::random(&mut OsRng),
            |x| x.sqrt_vartime(),
            BatchSize::SmallInput,
        )
    });
}

criterion_group!(
    benches,
    bench_mul,
    bench_division,
    bench_gcd,
    bench_shl,
    bench_shr,
    bench_inv_mod,
    bench_sqrt
);

criterion_main!(benches);
