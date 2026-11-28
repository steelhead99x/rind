//! Sets `cfg(graviola)` where the benches time Graviola: on the architectures
//! it builds for, unless `RIND_BENCH_NO_GRAVIOLA` is set. Graviola panics on
//! a CPU without the features it asserts, and listing the benchmarks runs
//! each once, so `admin/bench-report` sets it on such a host.

fn main() {
    println!("cargo::rustc-check-cfg=cfg(graviola)");
    println!("cargo::rerun-if-env-changed=RIND_BENCH_NO_GRAVIOLA");
    let arch = std::env::var("CARGO_CFG_TARGET_ARCH").unwrap();
    let refused = std::env::var_os("RIND_BENCH_NO_GRAVIOLA").is_some();
    if matches!(arch.as_str(), "x86_64" | "aarch64") && !refused {
        println!("cargo::rustc-cfg=graviola");
    }
}
