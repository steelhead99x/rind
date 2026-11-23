# [M] Harden sanitizers, fork safety, and 32-bit Miri coverage

## Goal

Nightly sanitizer and Miri jobs cover the blind spots found in the 2026-11-21 audit: ASan runs on the FFI bindings and denied CPU tiers, TSan and UBSan run with real concurrent stress tests (covering `ReuseCache`, `fips_rng`, and FFI handles), `rind-fips` detects `fork()` even when `pthread_atfork` is bypassed, and Miri checks `rind_limb="32"` 32-bit portable code.

## Plan

Planned with the maintainer on 2026-11-21 (`/quest-plan`): ✅ close the sanitizer, fork-safety, and 32-bit Miri gaps (rejected: skip).

- **ASan expansion**: run ASan against `rind-dart`, `rind-python`, `rind-fips`, and denied x86_64/aarch64 CPU tiers (in addition to host-default tiers) so fallback kernels and FFI pointer arithmetic get bounds and use-after-free checking.
- **TSan + UBSan + concurrent stress tests**: add nightly TSan and UBSan runs (for both Rust tests and any C/asm glue compiled with clang where applicable), and add multi-threaded stress tests hammering `ReuseCache`, `fips_rng` / global RNG state, lazy CPU-feature caches, and FFI handle lifecycles under contention.
- **Fork-safety hardening in `rind-fips`**: in `rind-fips/module/src/lib.rs`, add a `getpid()` check alongside `pthread_atfork` (matching the pattern already used when `clone()`/`SYS_fork` bypasses libc atfork handlers), plus a fork test that verifies parent and child produce distinct DRBG outputs even across raw fork.
- **32-bit Miri**: add a nightly Miri job targeting a 32-bit target (such as `i686-unknown-linux-gnu`) with `rind_limb="32"` so 32-bit portable limb arithmetic, pointer casts, and alignment assumptions are checked under Stacked/Tree Borrows.
- Update `TESTING.md` with the new sanitizer and Miri jobs.
