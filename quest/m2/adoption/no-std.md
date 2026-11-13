# [M] rind builds without std

## Goal

The `rind` crate is `#![no_std]` with `alloc`, and CI builds it for a target that has no `std`, so an embedded or kernel project, and any crate that is itself `no_std`, can depend on it. Nothing changes for a caller on a hosted target.

## Plan

Decided 2026-11-12 (maintainer, /quest-audit): ✅ a `no_std` build is one of the four ecosystem bets. RustCrypto's crates and ring are `no_std`, so a crate that promises its own users `no_std` cannot offer rind as a backend today, however the rest fits.

Where `rind` uses `std` on `main` that day, by `grep`, outside tests:

- Run-time CPU feature detection, in one `detect` function per backend: `is_x86_feature_detected!` in `rind/src/low/x86_64/cpu.rs:437`, `is_aarch64_feature_detected!` in `rind/src/low/aarch64/cpu.rs:179`, and `libc::getauxval` in `rind/src/low/arm/cpu.rs:67`, which needs no `std`. The macros' other uses, over a hundred lines of them, are in tests, mostly the generated assembly wrappers' `abi` checks, and can keep `std`.
- `std::env::var` in each backend's `test_toggle`, which reads `RIND_CPU_DISABLE_<id>` in debug builds and under `--cfg rind_cpu_disable` (`x86_64/cpu.rs:503`).
- `OnceLock`, three times, caching which SHA routine a CPU runs (`rind/src/low/x86_64/sha256_mux.rs:57` and its siblings).
- `thread_local!`, three times: the constant-time guard count (`rind/src/low/cpu.rs:121`), a debug-only check (`rind/src/low/entry.rs:8`), and the FIPS generator's per-thread state (`rind/src/fips_rng.rs:33`).
- `low/abi.rs`, and `Vec` and `Box`, which only need `alloc`.

The audit's recommendations, for whoever does this to confirm against the code:

- No `std` feature. A feature a dependent must remember to turn off is how `no_std` support rots, and rind has one way to do each job. Use `std` only under `cfg` for the targets that have an OS, and only for what needs one.
- x86_64 reads CPUID through `core::arch` with no OS. CPUID says what the CPU has, not what the OS switched on: `is_x86_feature_detected!` (`rind/src/low/x86_64/cpu.rs:440`), which is `std`'s, also reads XCR0 through XGETBV and reports AVX or AVX-512 only where the OS saves those registers. Whatever replaces it checks OSXSAVE and XCR0 the same way before it picks an AVX tier, or a kernel that never enabled them takes a fault on the first `vmovdqu`. aarch64 and arm have no portable way to ask from user code without one, so on a target with no OS a tier is chosen from the compile-time target features alone. PLATFORMS.md says so.
- An atomic replaces each `OnceLock`, since what it caches is a small enum computed the same on every thread.
- The guard count is per thread because the CPU's constant-time flag is. Without threads there is one count; say in the code what a `no_std` target with its own threads has to provide, or refuse to build the guard there until someone needs it.
- `getrandom` already supports targets without an OS through a caller-supplied source. rind passes that through and documents it; it does not grow a generator of its own.
- CI builds `rind` for one bare-metal target per architecture it has assembly for (such as `x86_64-unknown-none`, `aarch64-unknown-none`, and `armv7a-none-eabi`) on every PR, beside the wasm builds.
- The adapters stay on `std`: their upstreams' providers are.
- Removing a path that used `std` must not slow a hosted target: benchmark dispatch-heavy small inputs (SHA-256 at 64 B, AES-GCM at 128 B) before and after, against aws-lc-rs.

## Required

- [rind needs no runtime CPU check](/quest/m2/api/cpu-check.md) - CPU detection as this leaves it, which this then moves off `std`
