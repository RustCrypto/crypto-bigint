use criterion::{BatchSize, Criterion, black_box, criterion_group, criterion_main};
use crypto_bigint::{
    Limb, NonZero, Odd, Random, RandomBits, RandomMod, Reciprocal, U128, U256, U512, U1024, U2048,
    U4096, Uint,
};
use rand_chacha::ChaCha8Rng;
use rand_core::{RngCore, SeedableRng};

fn make_rng() -> ChaCha8Rng {
    ChaCha8Rng::from_seed(*b"01234567890123456789012345678901")
}

fn bench_random(c: &mut Criterion) {
    let mut group = c.benchmark_group("bounded random");

    let mut rng = make_rng();
    group.bench_function("random_mod, U1024", |b| {
        let bound = U1024::random(&mut rng);
        let bound_nz = NonZero::new(bound).unwrap();
        b.iter(|| black_box(U1024::random_mod(&mut rng, &bound_nz)));
    });

    let mut rng = make_rng();
    group.bench_function("random_bits, U1024", |b| {
        let bound = U1024::random(&mut rng);
        let bound_bits = bound.bits_vartime();
        b.iter(|| {
            let mut r = U1024::random_bits(&mut rng, bound_bits);
            while r >= bound {
                r = U1024::random_bits(&mut rng, bound_bits);
            }
            black_box(r)
        });
    });

    let mut rng = make_rng();
    group.bench_function("random_mod, U1024, small bound", |b| {
        let bound = U1024::from_u64(rng.next_u64());
        let bound_nz = NonZero::new(bound).unwrap();
        b.iter(|| black_box(U1024::random_mod(&mut rng, &bound_nz)));
    });

    let mut rng = make_rng();
    group.bench_function("random_bits, U1024, small bound", |b| {
        let bound = U1024::from_u64(rng.next_u64());
        let bound_bits = bound.bits_vartime();
        b.iter(|| {
            let mut r = U1024::random_bits(&mut rng, bound_bits);
            while r >= bound {
                r = U1024::random_bits(&mut rng, bound_bits);
            }
            black_box(r)
        });
    });

    let mut rng = make_rng();
    group.bench_function("random_mod, U1024, 512 bit bound low", |b| {
        let bound = U512::random(&mut rng);
        let bound = U1024::from((bound, U512::ZERO));
        let bound_nz = NonZero::new(bound).unwrap();
        b.iter(|| black_box(U1024::random_mod(&mut rng, &bound_nz)));
    });

    let mut rng = make_rng();
    group.bench_function("random_bits, U1024, 512 bit bound low", |b| {
        let bound = U512::random(&mut rng);
        let bound = U1024::from((bound, U512::ZERO));
        let bound_bits = bound.bits_vartime();
        b.iter(|| {
            let mut r = U1024::random_bits(&mut rng, bound_bits);
            while r >= bound {
                r = U1024::random_bits(&mut rng, bound_bits);
            }
            black_box(r)
        });
    });

    let mut rng = make_rng();
    group.bench_function("random_mod, U1024, 512 bit bound hi", |b| {
        let bound = U512::random(&mut rng);
        let bound = U1024::from((U512::ZERO, bound));
        let bound_nz = NonZero::new(bound).unwrap();
        b.iter(|| black_box(U1024::random_mod(&mut rng, &bound_nz)));
    });

    let mut rng = make_rng();
    group.bench_function("random_bits, U1024, 512 bit bound hi", |b| {
        let bound = U512::random(&mut rng);
        let bound = U1024::from((U512::ZERO, bound));
        let bound_bits = bound.bits_vartime();
        b.iter(|| {
            let mut r = U1024::random_bits(&mut rng, bound_bits);
            while r >= bound {
                r = U1024::random_bits(&mut rng, bound_bits);
            }
            black_box(r)
        });
    });

    // Slow case: the hi limb is just `2`
    let mut rng = make_rng();
    group.bench_function("random_mod, U1024, tiny high limb", |b| {
        let hex_1024 = "00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000291A6B42D1C7D2A7184D13E36F65773BBEFB4FA7996101300D49F09962A361F00";
        let modulus = U1024::from_be_hex(hex_1024);
        let modulus_nz = NonZero::new(modulus).unwrap();
        b.iter(|| black_box(U1024::random_mod(&mut rng, &modulus_nz)));
    });

    // Slow case: the hi limb is just `2`
    let mut rng = make_rng();
    group.bench_function("random_bits, U1024, tiny high limb", |b| {
        let hex_1024 = "00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000291A6B42D1C7D2A7184D13E36F65773BBEFB4FA7996101300D49F09962A361F00";
        let bound = U1024::from_be_hex(hex_1024);
        let bound_bits = bound.bits_vartime();
        b.iter(|| {
            let mut r = U1024::random_bits(&mut rng, bound_bits);
            while r >= bound {
                r = U1024::random_bits(&mut rng, bound_bits);
            }
        });
    });
}

fn bench_random_bits(c: &mut Criterion) {
    let mut group = c.benchmark_group("random_bits");

    let mut rng = make_rng();
    group.bench_function("random_bits, U256, full", |b| {
        b.iter(|| black_box(U256::random_bits(&mut rng, U256::BITS)));
    });

    group.bench_function("random_bits, U256, bounded", |b| {
        b.iter(|| black_box(U256::random_bits(&mut rng, 219)));
    });

    group.bench_function("random_bits, U2048, full", |b| {
        b.iter(|| black_box(U2048::random_bits(&mut rng, U2048::BITS)));
    });

    group.bench_function("random_bits, U2048, bounded", |b| {
        b.iter(|| black_box(U2048::random_bits(&mut rng, 1947)));
    });
}

fn bench_mul(c: &mut Criterion) {
    let mut group = c.benchmark_group("wrapping ops");

    let mut rng = make_rng();
    group.bench_function("split_mul, U256xU256", |b| {
        b.iter_batched(
            || (U256::random(&mut rng), U256::random(&mut rng)),
            |(x, y)| black_box(x.split_mul(&y)),
            BatchSize::SmallInput,
        )
    });

    group.bench_function("split_mul, U4096xU4096", |b| {
        b.iter_batched(
            || (U4096::random(&mut rng), U4096::random(&mut rng)),
            |(x, y)| black_box(x.split_mul(&y)),
            BatchSize::SmallInput,
        )
    });

    group.bench_function("square_wide, U256", |b| {
        b.iter_batched(
            || U256::random(&mut rng),
            |x| black_box(x.square_wide()),
            BatchSize::SmallInput,
        )
    });

    group.bench_function("square_wide, U4096", |b| {
        b.iter_batched(
            || U4096::random(&mut rng),
            |x| black_box(x.square_wide()),
            BatchSize::SmallInput,
        )
    });

    group.bench_function("mul_mod, U256", |b| {
        b.iter_batched(
            || {
                let m = Odd::<U256>::random(&mut rng);
                let x = U256::random_mod(&mut rng, m.as_nz_ref());
                (m.to_nz().unwrap(), x)
            },
            |(m, x)| black_box(x).mul_mod(black_box(&x), &m),
            BatchSize::SmallInput,
        )
    });

    group.bench_function("mul_mod_vartime, U256", |b| {
        b.iter_batched(
            || {
                let m = Odd::<U256>::random(&mut rng);
                let x = U256::random_mod(&mut rng, m.as_nz_ref());
                (m.to_nz().unwrap(), x)
            },
            |(m, x)| black_box(x).mul_mod_vartime(black_box(&x), &m),
            BatchSize::SmallInput,
        )
    });

    group.bench_function("mul_mod_special, U256", |b| {
        b.iter_batched(
            || {
                let m = Limb::random(&mut rng);
                let x = U256::random(&mut rng);
                (m, x)
            },
            |(m, x)| black_box(x).mul_mod_special(black_box(&x), m),
            BatchSize::SmallInput,
        )
    });
}

fn bench_division(c: &mut Criterion) {
    let mut rng = make_rng();
    let mut group = c.benchmark_group("wrapping ops");

    group.bench_function("div/rem, U256/U128, full size", |b| {
        b.iter_batched(
            || {
                let x = U256::random(&mut rng);
                let y_half = U128::random(&mut rng);
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
                let x = U256::random(&mut rng);
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
                let x = U256::random(&mut rng);
                let y_half = U128::random(&mut rng);
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
                let x = U256::random(&mut rng);
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
                let (x_lo, x_hi) = (U256::random(&mut rng), U256::random(&mut rng));
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
                let x = U256::random(&mut rng);
                let y_small = Limb::random(&mut rng);
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
                let x = U256::random(&mut rng);
                let y = Limb::random(&mut rng);
                (x, NonZero::new(y).unwrap())
            },
            |(x, y)| black_box(x.div_rem_limb(y)),
            BatchSize::SmallInput,
        )
    });

    group.bench_function("div/rem, U256/Limb, single limb with reciprocal", |b| {
        b.iter_batched(
            || {
                let x = U256::random(&mut rng);
                let mut y = Limb::random(&mut rng);
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
    let mut rng = make_rng();
    let mut group = c.benchmark_group("greatest common divisor");

    group.bench_function("gcd, U256", |b| {
        b.iter_batched(
            || {
                let f = U256::random(&mut rng);
                let g = U256::random(&mut rng);
                (f, g)
            },
            |(f, g)| black_box(f.gcd(&g)),
            BatchSize::SmallInput,
        )
    });

    group.bench_function("gcd_vartime, U256", |b| {
        b.iter_batched(
            || {
                let f = Odd::<U256>::random(&mut rng);
                let g = U256::random(&mut rng);
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
    let mut rng = make_rng();
    let mut group = c.benchmark_group("modular ops");

    group.bench_function("inv_odd_mod, U256", |b| {
        b.iter_batched(
            || {
                let m = Odd::<U256>::random(&mut rng);
                loop {
                    let x = U256::random(&mut rng);
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
                let m = Odd::<U256>::random(&mut rng);
                loop {
                    let x = U256::random(&mut rng);
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
                let m = U256::random(&mut rng);
                loop {
                    let x = U256::random(&mut rng);
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
    let mut rng = make_rng();
    let mut group = c.benchmark_group("sqrt");

    group.bench_function("sqrt, U256", |b| {
        b.iter_batched(
            || U256::random(&mut rng),
            |x| x.sqrt(),
            BatchSize::SmallInput,
        )
    });

    group.bench_function("sqrt_vartime, U256", |b| {
        b.iter_batched(
            || U256::random(&mut rng),
            |x| x.sqrt_vartime(),
            BatchSize::SmallInput,
        )
    });
}

criterion_group!(
    benches,
    bench_random,
    bench_random_bits,
    bench_mul,
    bench_division,
    bench_gcd,
    bench_shl,
    bench_shr,
    bench_inv_mod,
    bench_sqrt
);

criterion_main!(benches);
