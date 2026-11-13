# [M] Ed25519 verification uses half-size scalars

## Goal

Verifying one Ed25519 signature runs a multi-scalar multiplication over scalars of about 128 bits instead of 253, so it does about half the doublings, and it accepts exactly the signatures it accepts today. BENCHMARKS.md shows the gain against aws-lc-rs on every tier that takes it.

## Plan

Decided 2026-11-12 (maintainer, /quest-audit): ✅ single verification only (rejected: a batch verification API too; neither).

- The method, as the audit found it: a 2025 TCHES paper on halving the scalars in EdDSA verification, which rewrites `[S]B = R + [k]A` with a short multiplier found by a half-GCD on `k`, and an implementation in `solana-ed25519` under BSD-3-Clause that reports about 15%. The audit did not read the paper or the code. Before writing any, confirm the paper, the license, and the gain, and stop with what you found if any of the three does not hold.
- Acceptance must not change. Multiplying the equation through by a scalar changes what a point with a torsion component does to it, and Ed25519 libraries already disagree on those inputs. rind follows aws-lc-rs, so the new path agrees with the old one and with aws-lc-rs on Wycheproof, on the small-order and mixed-order vectors (the "Taming the many EdDSAs" set), on non-canonical `R` and `S`, and differentially on random and mutated signatures. A vector the two paths split on ends the quest, not the old path.
- Verification handles only public values, so nothing here needs to be constant time. Say so where the half-GCD is written, since it is variable time by nature.
- New arithmetic states where its correctness comes from (AGENTS.md): the paper's argument for the rewritten equation, and the tests above.
- It costs a ✓. `benchmarks/verified.toml` gives `ed25519-verify` the ✓ on aarch64 and on Intel CPUs with AVX but not AVX2, both resting on s2n-bignum's proof of `edwards25519_scalarmuldouble`, which `rind/src/mid/ed25519.rs:149` calls to recompute `R`. A different multi-scalar routine there is unproven until someone proves it. AGENTS.md says to run the fastest and plan its proof, so where the gain measures, take it, drop the tier from the ✓ row, and plan the proof as a quest of its own in the same PR. A tier where it does not measure keeps its proven routine.
- It changes the routine [Ed25519 verification on AVX2 without ADX](/quest/m4/verified/ed25519-avx2-verify.md) is proving, which has a draft PR ([kixel-ai/rind#646](https://github.com/kixel-ai/rind/pull/646)). Tell the maintainer before replacing that tier's routine: the proof either lands first and is then redone, or retargets.
- Benchmark each tier against aws-lc-rs before and after, on the report's hosts.

## Related

- [Ed25519 verification on AVX2 without ADX is proven](/quest/m4/verified/ed25519-avx2-verify.md) - proves the routine this would replace on that tier
