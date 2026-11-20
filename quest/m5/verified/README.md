# Every cold tier is proven

## Goal

Every operation rind exports earns `benchmarks/verified.toml`'s strict ✓ on the tiers few machines run: armv7, the legacy hashes, and x86_64 and aarch64 without AES or SHA hardware.

## Plan

Moved from [the m4 verified epic](/quest/m4/verified/README.md) with the maintainer on 2026-11-09, so the hot tiers' proofs rank ahead of these. That epic's rules hold here: prove the code rind runs under [the m4 epic's composition rule](/quest/m4/verified/README.md#composition-rule). New assembly proofs go in Lean on pyca/verified-garbage's models once [the trial](/quest/m2/lean-assembly-trial.md) sets the route, except where its PR and the maintainer pick HOL Light for a routine until [the port](/quest/m5/verified/hol-light-to-lean.md) (maintainer, 2026-11-18), and rind's existing HOL Light proofs [are ported](/quest/m5/verified/hol-light-to-lean.md).

Under `AGENTS.md`'s speed rule (maintainer, 2026-11-09: ✅ the fastest source, then its proof; rejected: verified code within about 10% on cold tiers, or everywhere), these tiers run their fastest source unproven until a quest here proves it. A verified source replaces one only where it measures as fast at every size.

## Required

- [armv7 is proven](/quest/m5/verified-armv7/README.md) - an AArch32 model, then armv7's assembly, curves, and Rust
