# [M] Every published function runs under a test

## Goal

The nightly coverage report, on both Linux/x86_64 and macOS/aarch64, lists no function in the published code that never runs. Each one it listed gets a test that reaches it, or is deleted as dead code. A function only another architecture compiles counts as covered when that architecture's run reaches it.

## Plan

Planned with the maintainer on 2026-11-12, with the coverage report's goal: no percentage target, just no unrun function left without a reason.

On the 2026-11-12 macOS run, before the port of aws-lc-rs's tests and the report changes, the unrun functions outside rind-aws-lc-rs and the tools were:

- `rind`: 53 of 2,129 (20 in `high/`, 15 in `mid/`, 18 in `low/`), for example in `high/signature.rs`, `high/hpke.rs`, `mid/mldsa.rs`, `mid/mlkem768.rs`, and `low/aarch64/mldsa.rs`.
- rind-ring: 33 of 213, mostly in `aead.rs` and `agreement.rs`.
- rind-dart: 34 of 199. Measured under `dart test`, 1 is left on the 2026-11-12 Linux run.
- Smaller gaps: rind-str0m 14, rind-dimpl 13, rind-rcgen 10, rind-rustls 10, rind-object-store 3, rind-jsonwebtoken 1.

Guidance:

- Start from the report as the port of aws-lc-rs's tests leaves it, and recount: `admin/coverage` now measures rind-dart under `dart test` and pyrind under `sh/python.sh test`, and leaves the tools out, and the port reaches much of the adapters.
- Test behavior a caller can see, such as an error path on malformed input or an accessor compared with the upstream crate's value. A `Debug` or `Display` impl needs a test only where callers rely on its output.
- Where a function is unreachable from any public path, delete it rather than test it.
- Where only a CPU feature neither runner has reaches a function, say so in [TESTING.md](/TESTING.md) instead of leaving it silent.

## Required

- [rind-aws-lc-rs runs aws-lc-rs's in-crate tests of its public API](/quest/m2/confidence/aws-lc-rs-unit-tests.md) - closes most of rind-aws-lc-rs's remaining gap first, so no test is written twice

## Related

- [Adapter crates' surviving mutants](/quest/m2/confidence/mutants-adapters.md) - kills mutants in the same adapter code; tests written here may kill some
