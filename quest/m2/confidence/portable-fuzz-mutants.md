# [M] The portable backend is fuzzed and mutation tested

## Goal

Every fuzz target also runs against the portable backend nightly, and a mutation campaign reaches every file only that backend compiles. Each mutant there that no test catches is killed by a test or recorded with its reason. [TESTING.md](/TESTING.md)'s portable row no longer says "none" for fuzzing.

## Plan

Planned from the 2026-11-09 tooling audit. Every architecture m2's targets epic adds, and wasm32, ships on this backend alone, and it is the least checked:

- Fuzzing: `TESTING.md:58` says "none: fuzz jobs build the native backends". `fuzz.yml:51-58` builds each target once per runner architecture, and `sh/fuzz-replay.sh:43` refuses any other.
- Mutation: `admin/mutants` has a campaign for x86_64, aarch64, armv7, and macOS's DIT code, and exits on anything else. cargo-mutants mutates code whatever its `cfg`, so on the 64-bit hosts a mutant in `rind/src/low/portable/` or `rind/src/mid/portable/` is never compiled, and no test can catch it.
- `admin/mutants --target armv7-unknown-linux-gnueabihf` runs under qemu and reaches what armv7 shares with the portable backend. It skips what armv7's assembly replaces: `rind/src/low/portable/{chacha20,cpu,keccak,sha}.rs`, and `low/generic/mont.rs`'s `mont_sqr` and `mont_mul_limbs`, whose mutants no campaign catches. No campaign reaches those.

Guidance:

- Force the backend on x86_64 with `--cfg rind_portable --cfg curve25519_dalek_backend="serial"`, as `sh/portable.sh:29` does, so neither check needs an emulator.
- Fuzz it, don't only replay. The portable backend is Rust, so libFuzzer's coverage sees inside it, which it cannot in the assembly backends. Replay the native corpus too, since those inputs are free. Keep each target's corpus for this backend apart from the native one.
- Mutation: give `admin/mutants` a portable campaign that skips the three assembly backends and has no feature rows, since the backend reads no CPU features. It may mutate the whole backend or only what armv7's campaign skips, whichever is simpler to keep right.
- Both run nightly, in `fuzz.yml` and `mutants.yml`, not in `just ci`.
- Record survivors in `.cargo/mutants.toml` as the other campaigns do.

## Related

- [rind runs in OSS-Fuzz](/quest/m4/oss-fuzz.md) - would fuzz this build continuously once it exists
