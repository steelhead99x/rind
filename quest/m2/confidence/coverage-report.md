# [M] The coverage report measures the published code under its own tests

## Goal

The nightly `coverage.yml` report covers exactly the code rind publishes: the `rind` crate and every adapter on crates.io, plus rind-dart (pub.dev) and rind-python (PyPI, as `pyrind`), each measured under the tests that actually call it. Tools are left out. A function the report lists as never run is published code that no test reaches.

## Plan

Planned with the maintainer on 2026-11-12, after a question about rind's `cargo llvm-cov` numbers.

- Goal: every function in the published crates runs under a test, and the report measures only those crates. ✅ No percentage floor or target (rejected: fail nightly below a set function percentage), since a floor is an arbitrary acceptance criterion.
- rind-dart: ✅ measure what the Dart tests reach (rejected: Rust tests that call the FFI functions directly, which duplicate the Dart tests; leaving rind-dart out of the report). The same reasoning applies to rind-python and its pytest suite.

Facts from the 2026-11-12 nightly run (macOS/aarch64, then Linux/x86_64):

- Whole workspace: 82.9% / 84.0% of functions, 95.6% / 96.9% of lines.
- The tools drag the function figure down: rind-timing runs in `timing.yml`, not under tests, and has 234 of 244 functions unrun. rind-cpuid, rind-bench, and `fuzz/` are also tools. Leave all four out of the report, as `.cargo/mutants.toml` already leaves out three of them.
- rind-dart shows 34 of 199 functions unrun because `admin/coverage` never runs `dart test`. rind-python is missing from the report entirely.
- Each generated assembly file is one huge function, always fully covered, which inflates the line figure. That is accurate, not a bug: leave it in.

Guidance:

- `cargo llvm-cov show-env` already exports the instrumentation flags, so `admin/coverage` can build rind-dart's library and rind-python's extension in that environment, then run `dart test` and pytest against them before `cargo llvm-cov report`. The coverage dev shell then needs the Dart SDK and Python, which `flake.nix`'s `dart` and Python shells already pin.
- `admin/coverage` ends with `cargo run --example client https://jbp.io`, which reaches the network. Check whether that example still exists and earns a place in the report.
- A plain local `cargo llvm-cov` reports less than the nightly run, since it skips the Wycheproof, CAVP, and CCTV submodules, `SLOW_TESTS=1`, and the CPU-feature reruns. Say in [TESTING.md](/TESTING.md) that `admin/coverage` is the way to measure, and where the nightly report is.

## Related

- [cargo-llvm-cov builds with its tests again](/quest/m3/cargo-llvm-cov-check.md) - the coverage dev shell's packaging wait
