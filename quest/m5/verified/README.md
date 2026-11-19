# Every cold tier is proven

## Goal

Every operation rind exports earns `benchmarks/verified.toml`'s strict ✓ on the tiers few machines run: armv7, the legacy hashes, and x86_64 and aarch64 without AES or SHA hardware.

## Plan

Moved from [the m4 verified epic](/quest/m4/verified/README.md) with the maintainer on 2026-11-09, so the hot tiers' proofs rank ahead of these. That epic's rules hold here: prove the code rind runs, in HOL Light or Lean, under [the m4 epic's composition rule](/quest/m4/verified/README.md#composition-rule).

Under `AGENTS.md`'s speed rule (maintainer, 2026-11-09: ✅ the fastest source, then its proof; rejected: verified code within about 10% on cold tiers, or everywhere), these tiers run their fastest source unproven until a quest here proves it. A verified source replaces one only where it measures as fast at every size.

## Required

- [armv7 is proven](/quest/m5/verified-armv7/README.md) - an AArch32 model, then armv7's assembly, curves, and Rust
