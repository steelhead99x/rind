# [S] Mutation testing with wipe on x86_64 and aarch64

## Goal

The x86_64 and aarch64 runs of `mutants.yml` build rind with its `wipe` feature, as the armv7 run does, so `rind/tests/zeroing.rs` catches a mutant that stops a key's `Drop` wiping it. Every survivor this adds is killed by a test or recorded in `.cargo/mutants.toml` with why no test can.

## Plan

Kept by the maintainer on 2026-11-10, when picking [moq-dev/rind#538](https://github.com/moq-dev/rind/pull/538) to merge: ✅ keep (rejected: drop). Without `wipe`, each `Drop` that wipes a key, such as `mid/ed25519.rs`'s `SigningKey::drop`, survives on both architectures, since `zeroise` does nothing.

- Add `--features rind/wipe` to the x86_64 and aarch64 matrix entries' `args`. `--workspace` takes a package-qualified feature, and rind-aws-lc-rs's own `wipe` then stays off, as its default is.
- Run `admin/mutants --workspace --features rind/wipe` over `rind/src` on each architecture, and kill or record what survives. The `Drop` exclusions under "Wipes a key inside a type whose own `Drop` wipes all of it" stay: `zeroing.rs` checks the outer type, which wipes every byte anyway.
- If [the wipe default](/quest/m2/wipe-default.md) turns `wipe` on by default first, the flag is redundant: drop the matrix change and only run the campaign.

## Related

- [Measure what wiping costs](/quest/m2/wipe-default.md) - may make `wipe` the default, which turns it on here without a flag
