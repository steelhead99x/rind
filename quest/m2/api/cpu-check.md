# [S] rind needs no runtime CPU check

## Goal

A backend requires only its target's compile-time features, so no CPU that runs a rind binary lacks one. `rind::cpu::check`, `cpu::MissingFeature`, and the panic every operation guards against are gone, and pyrind, rind-dart, and rind-cpuid stop calling the check.

## Plan

`check()` can no longer fail on any target rind builds for. `missing_cpu_feature()` returns `None` on x86_64, arm, and portable, and aarch64 checks only `neon`, which every aarch64 target with `std` enables at compile time (`rustc --print cfg`, 2026-11-08); only the `no_std` `*-none-softfloat` targets lack it. The check dates from [moq-dev/rind#12](https://github.com/moq-dev/rind/pull/12), when x86_64 required AVX2, ADX, BMI2, and AES-NI, requirements that later tiers removed ([moq-dev/rind#172](https://github.com/moq-dev/rind/pull/172), [moq-dev/rind#178](https://github.com/moq-dev/rind/pull/178)).

Decided with the maintainer on 2026-11-08:

- Delete the runtime check and make requirements compile-time ✅ (rejected: keep `check()` documented as never failing; leave it). rind's removal ships in 0.4.
- `rind/build.rs` selects the aarch64 backend only when `CARGO_CFG_TARGET_FEATURE` has `neon`, and the portable backend otherwise, which is one backend per target, chosen at build time.
- AGENTS.md's Required rule changes from "a CPU missing a required feature fails with an error naming it" to say a backend requires only its target's compile-time features. The maintainer asked for this edit; follow `quest guide prompting`.
- The adapters stopped calling `check()` and dropped their `MissingFeature` in [moq-dev/rind#522](https://github.com/moq-dev/rind/pull/522), [moq-dev/rind#521](https://github.com/moq-dev/rind/pull/521), [moq-dev/rind#516](https://github.com/moq-dev/rind/pull/516), [moq-dev/rind#515](https://github.com/moq-dev/rind/pull/515), and [moq-dev/rind#519](https://github.com/moq-dev/rind/pull/519), since their upstreams have no such error. That work also replaces this quest's earlier decision to break the adapters in patch releases for this quest alone.
- Delete what only existed for the check: `verify_cpu_features` and its per-operation atomic load in `low::entry`, `rind/tests/cpu.rs`'s per-feature panic test, and `RIND_CPU_DISABLE_neon` if nothing else uses it. Keep the optional-feature toggles that select tiers.
- Update README, PLATFORMS.md, MIGRATING.md, and ARCHITECTURE.md's `cpu` line, which tell callers to check first. Keep `cpu::has_aes_hardware` and `cpu::Dit`.
