use gungraun::{Callgrind, LibraryBenchmarkConfig, library_benchmark_group, main};

mod ct_uint_ops;
mod ct_uint_cmp_vartime;
mod ct_uint_gcd;
mod ct_uint_modpow;
mod utils;

pub use ct_uint_ops::bench_u1024_wrapping_add;
pub use ct_uint_ops::bench_u1024_wrapping_sub;
pub use ct_uint_ops::bench_u1024_wrapping_mul;
pub use ct_uint_cmp_vartime::bench_u1024_cmp_vartime;
pub use ct_uint_gcd::bench_u1024_gcd;
pub use ct_uint_modpow::bench_u1024_modpow;

library_benchmark_group!(
    name = uint_mul_wrapping;
    benchmarks = bench_u1024_wrapping_mul
);

library_benchmark_group!(
    name = uint_add_wrapping;
    benchmarks = bench_u1024_wrapping_add
);

library_benchmark_group!(
    name = uint_sub_wrapping;
    benchmarks = bench_u1024_wrapping_sub
);

library_benchmark_group!(
    name = uint_gcd;
    benchmarks = bench_u1024_gcd
);

library_benchmark_group!(
    name = uint_modpow;
    benchmarks = bench_u1024_modpow
);

library_benchmark_group!(
    name = uint_cmp_vartime;
    benchmarks = bench_u1024_cmp_vartime
);

main!(
    config = LibraryBenchmarkConfig::default().tool(Callgrind::default());
    library_benchmark_groups =
        uint_mul_wrapping,
        uint_add_wrapping,
        uint_sub_wrapping,
        uint_gcd,
        uint_modpow,
        uint_cmp_vartime
);
