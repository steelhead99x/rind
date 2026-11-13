# [XS] main's nine surviving mutants

## Goal

The next mutation campaign over `rind/src/high/vrf.rs`, `rind/src/mid/p256.rs`, and `rind/src/low/x86_64/aes.rs` reports no survivors. The nine mutants that [run 43374165087](https://github.com/kixel-ai/rind/actions/runs/43374165087) found on `main`'s code, while validating [kixel-ai/rind#717](https://github.com/kixel-ai/rind/pull/717), are killed by tests or excluded as equivalent with a stated reason.

## Plan

Decided 2026-11-13 (maintainer, /quest-run follow-up): ✅ plan it (rejected: leave it).

The survivors came from code that landed after `0f4e45f0`. The nightly that would have reported them was cancelled by `mutants.yml`'s old shared concurrency group.

- Seven in `vrf.rs` need tests. Six are `Debug` impls replaced with `Ok(Default::default())`: `Algorithm`, `SecretKey`, `SecretKeyBytes`, `PublicKey`, `Proof`, and `Output`. Add them to `rind/tests/debug.rs`, which already pins the `rind` crate's `Debug` output and checks that no secret shows. The adapters' `Debug` survivors stay excluded ([the adapters' quest](/quest/m2/confidence/mutants-adapters.md)), but that decision covers only the adapter crates. The seventh, `<impl PartialEq for Algorithm>::eq` replaced with `true`, needs a test that the two suites' algorithms compare unequal.
- Two are equivalent `|` to `^` mutants: in `Point::to_compressed` (`p256.rs:299`), `0x02` and the parity bit `y & 1` never share a bit, and in `store` (`x86_64/aes.rs:510`), `hi << 64` and `lo` never do. Add both to the "Equivalent: an OR of values that never share a set bit" block of `exclude_re` in `.cargo/mutants.toml`, matching by function name, as its other entries do, rather than by line.
- Confirm with `admin/mutants --file` on the three files, which counts as scoped on the agent hosts. `aes.rs` is x86_64-only, so run that one on an x86_64 host.
- [kixel-ai/rind#722](https://github.com/kixel-ai/rind/pull/722) also edits `vrf.rs`. Whichever lands second takes the other's line numbers.

## Related

- [Whole mutation campaigns run on GitHub-hosted runners](/quest/m0/mutants-hosted.md) - the dispatch that found these
