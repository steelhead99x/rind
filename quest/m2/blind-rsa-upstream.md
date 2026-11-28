# [S] Return to blind-rsa-signatures 0.19

## Goal

`thirdparty/blind-rsa-signatures`, rind's fork ported to `rsa` 0.10.0, is deleted: blind-rsa-signatures 0.19.0 builds on it, so the workspace takes the release from crates.io and `[patch.crates-io]` loses the entry.

## Plan

Found by the 2026-11-21 dependency audit. blind-rsa-signatures 0.19.0 was published on 2026-11-18, and its manifest requires `rsa` `^0.10.0` and `crypto-bigint` `^0.7.11`. Its "Update deps" commit (`3142fbb`) makes the changes `thirdparty/blind-rsa-signatures/RIND.md` lists: the `PrivateKeyParts` port (`Odd<BoxedUint>` primes, `p()` and `q()`), the renamed `PrivateKey` and `PublicKey`, and `bit_width`. The audit built it alone against `rsa` 0.10.0 (`cargo check` passes) but not against the workspace's tests, so start there.

- Wait out the cooldown: `sh/cooldown.sh` fails a lockfile that gains a release younger than 7 days, so the lock can take 0.19.0 from 2026-11-26 (the `Scheduled` date).
- Change the three manifests that name it (`rind/Cargo.toml`, `fuzz/Cargo.toml`, `rind-bench/Cargo.toml`) from 0.18 to 0.19, delete `thirdparty/blind-rsa-signatures`, the `[patch.crates-io]` entry and its comment, and the `exclude` in `Cargo.toml`, and `cargo update -p blind-rsa-signatures`.
- Take 0.19.0's vectors: `admin/sync-vectors`'s `BLIND_RSA` is `45d0abfa`, the 0.18.0 tree. Move it to the 0.19.0 tag's commit, rerun `admin/sync-vectors`, and update `AUDIT.md`'s row (`admin/audit` checks it).
- Remove `UPSTREAM.md`'s "blind-rsa-signatures 0.18 does not build on rsa 0.10.0", and `admin/upstream`'s `blind-rsa-signatures` case. The `0.18.0` in `benchmarks/data/*.json` is a past run's record: leave it.
- Run `rind`'s `crosschecks` blind RSA tests and the `blind_rsa` fuzz target. If a vector or a behavior differs from the fork's, the fork's changes were not all upstream's: keep the fork and list what differs in `RIND.md`.
- The fork's `crypto-primes` is pinned `=0.7.0` and the fork never uses it; 0.19.0 requires `^0.7.2`, which moves the lock's `crypto-primes` with it.

## Scheduled

- 2026-11-26 - the first day 0.19.0 is past the 7-day cooldown
