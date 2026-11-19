# [S] ML-DSA's key pair wipes every byte on macOS

## Goal

`rind/tests/zeroing.rs`'s `ml_dsa` test passes on every run on macOS/aarch64, because an ML-DSA key pair wipes its whole value on drop there, as AGENTS.md requires. The cause of its occasional failure is found and fixed, not hidden by a retry or a looser check.

## Plan

Found by [the uncovered-functions quest](https://github.com/kixel-ai/rind/pull/862) while reading main's red nightlies.

- What failed: the nightly `coverage` workflow's macOS job, [run 43997727786](https://github.com/kixel-ai/rind/actions/runs/43997727786) (2026-11-17), `byte 3968 (0x1) was not cleared after drop` for a 4016-byte value, the ML-DSA-44 `KeyPair::from_seed` the test checks third. It passed in the other macOS runs and on a local M-series Mac.
- The test drops in place and reads the memory before freeing it, so another allocation cannot have reused the bytes. `mid::mldsa::KeyPair`'s drop wipes all `size_of::<Self>()` bytes, padding included, so a nonzero byte is either outside the value that drop wipes (a field of a wrapping type, such as the public key) or a write after the wipe, such as a field's drop glue or a lazily filled cache.
- Reproduce it first, for example by looping the test on macOS with and without `RIND_CPU_DISABLE_sha3=1` (the coverage job runs both), and print which field sits at that offset, then fix the wipe at its root.

## Related

- [Failures show up on the PR that causes them](/quest/m0/catch-on-pr/README.md) - this failure turns main's nightly red for changes that didn't cause it.
