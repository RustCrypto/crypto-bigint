# Gungraun-Based Constant-Time Benchmarks

This directory contains the gungraun benchmarks and helper tooling used to
inspect the instruction-count behavior operations in
`crypto-bigint`.

## Running the benchmarks

The `ct_gungraun` bench is defined in `Cargo.toml` as a single bench
target which uses the gungraun harness in `benches/gungraun/mod.rs`:

```bash
cargo bench --bench ct_gungraun --features "gungraun rand"
```

To collect Callgrind summaries (used by the checker in CI), enable
`GUNGRAUN_SAVE_SUMMARY`:

```bash
GUNGRAUN_SAVE_SUMMARY=json \
cargo bench --bench ct_gungraun --features "gungraun rand"
``` 

This populates `target/gungraun/` with per-case `summary.json` files.

## Constant-time checker

There is an integration test `tests/check_ct_gungraun.rs` which parses
the gungraun `summary.json` files, extracts Callgrind’s `Ir` (instruction
count) metric, and enforces constant-time behavior:

- Groups whose module path contains `vartime` are **skipped**
  (e.g. `uint_cmp_vartime`).
- All other groups are treated as constant-time and must have identical
  `Ir` across all their benchmark cases.

Usage (after running the bench with summaries enabled):

```bash
cargo test --test check_ct_gungraun
```

If everything is as expected, the test passes and prints a summary like:

```text
Constant-time check passed: N const-time groups, M vartime groups skipped.
```

If any constant-time group has differing `Ir` values across cases, the
test prints a diagnostic and fails, which is intended to fail CI.

## Adding new benchmarks

For a new constant-time operation:

1. Create a new `ct_*` file (e.g. `ct_uint_foo.rs`) that:
   - Uses `#[library_benchmark]` and `#[bench::...]` or
     `#[benches::with_iter(...)]` to define cases.
   - Keeps the function name and module path *without* `vartime` in the
     name (so the checker will enforce constant-time behavior).
2. Re-export the function in `mod.rs` and add it to a
   `library_benchmark_group!` that is included in the `main!` macro.
3. Re-run:
   - `GUNGRAUN_SAVE_SUMMARY=json cargo bench --bench ct_gungraun --features "gungraun rand"`
   - `cargo test --test check_ct_gungraun`

For a new **variable-time** operation (for comparison only), include
`vartime` in the module path or function name so that the checker skips
it automatically.***
