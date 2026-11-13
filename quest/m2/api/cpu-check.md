# [S] rind needs no runtime CPU check

## Goal

A backend requires only its target's compile-time features, so no CPU that runs a rind binary lacks one. `rind::cpu::check`, `cpu::MissingFeature`, and the panic every operation guards against are gone, and pyrind, rind-dart, and rind-cpuid stop calling the check.

## Plan

`check()` can no longer fail on any target rind builds for. `missing_cpu_feature()` returns `None` on x86_64, arm, and portable, and aarch64 checks only `neon`, which every aarch64 target with `std` enables at compile time (`rustc --print cfg`, 2026-11-08); only the `no_std` `*-none-softfloat` targets lack it. The check dates from [kixel-ai/rind#12](https://github.com/kixel-ai/rind/pull/12), when x86_64 required AVX2, ADX, BMI2, and AES-NI, requirements that later tiers removed ([kixel-ai/rind#172](https://github.com/kixel-ai/rind/pull/172), [kixel-ai/rind#178](https://github.com/kixel-ai/rind/pull/178)).

Decided with the maintainer on 2026-11-08:

- Delete the runtime check and make requirements compile-time ✅ (rejected: keep `check()` documented as never failing; leave it). rind's removal ships in 0.4.
- `rind/build.rs` selects the aarch64 backend only when `CARGO_CFG_TARGET_FEATURE` has `neon`, and the portable backend otherwise, which is one backend per target, chosen at build time.
- AGENTS.md's Required rule changes from "a CPU missing a required feature fails with an error naming it" to say a backend requires only its target's compile-time features. The maintainer asked for this edit; follow `quest guide prompting`.
- The adapters no longer call `check()` or have a `MissingFeature`, since their upstreams have no such error. Their fixes ship with rind 0.4 in [rind 0.4 ships once](/quest/m2/api/release-0.4.md), so this quest removes only rind's own check.
- Delete what only existed for the check: `verify_cpu_features` and its per-operation atomic load in `low::entry`, `rind/tests/cpu.rs`'s per-feature panic test, and `RIND_CPU_DISABLE_neon` if nothing else uses it. Keep the optional-feature toggles that select tiers.
- Update README, PLATFORMS.md, MIGRATING.md, MIGRATE.md, TESTING.md, and ARCHITECTURE.md's `cpu` line, which tell callers to check first. Keep `cpu::has_aes_hardware` and `cpu::Dit`.
