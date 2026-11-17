# [XS] desktop measures SHA-512 on the AVX2 routine

## Goal

`benchmarks/data/desktop.json` times rind's SHA-512 and Ed25519 signing on Arrow Lake as rind runs them since [kixel-ai/rind#821](https://github.com/kixel-ai/rind/pull/821), on OpenSSL's AVX2 routine rather than the SHA512 instructions, so BENCHMARKS.md's `desktop` section shows them again and the SHA-512 loss against aws-lc-rs is measured at the bar's hash sizes.

## Plan

- #821 dropped those four rind rows from `desktop.json`, which timed the removed routine (60 ns, 249 ns, and 2.63 µs at 64 B, 1350 B, and 16 KB, against aws-lc-rs's 134 ns, 1.24 µs, and 14.12 µs) and would have shown under a ✓ only the AVX2 routine earns. On a shared Sapphire Rapids-class Xeon without the instructions, the AVX2 routine measured 0.78x, 0.90x, and 0.92x aws-lc-rs's time at those sizes (2026-11-17).
- Run `admin/bench-report collect --host desktop` at `main`, then `admin/bench-report render`, and record in the PR the AVX2 routine's time over aws-lc-rs's and over the old 60 ns, 249 ns, and 2.63 µs. It needs the SSH access to `desktop` that `admin/bench-report collect` uses.
- Revisiting the SHA512 instructions themselves, if Intel lists them, is [their own quest](/quest/m4/verified/sha512-x86-ext.md).
