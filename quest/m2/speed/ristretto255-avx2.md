# [M] ristretto255's variable-base multiplication runs curve25519-dalek's AVX2 formulas

## Goal

On x86_64 with AVX2 but without ADX, ristretto255's constant-time variable-base multiplication (OPRF blind and evaluate, VRF) runs curve25519-dalek's AVX2 field and point formulas, as Ed25519 verification without ADX already does, closing the 1.18 to 1.30× gap to RustCrypto's `voprf` that `benchmarks/gaps.toml`'s OPRF entry records.

## Plan

Decided 2026-11-18 (maintainer, [kixel-ai/rind#619](https://github.com/kixel-ai/rind/pull/619#issuecomment-6994276361)): ✅ keep this quest, ✅ worth the unproven constant-time port under the fastest-source rule (rejected: not until something calls OPRF or VRF on a hot path, planned in m4).

- Today `mid/ristretto255.rs`'s `Element::mul` runs a four-bit fixed window over s2n-bignum's field arithmetic. dalek's AVX2 backend is already ported in `low/x86_64/edwards25519_msm_avx2.rs` for Ed25519 verification, but that one is variable time over public scalars: this needs dalek's constant-time variable-base multiplication (`vartime` off: a fixed window with constant-time table selection), reusing the ported field and point layers.
- Measured on `nixos`, `ovh-iad`, and `ovh-sea` in the 0.4 report refresh: blinding 1.18 to 1.25× and evaluation 1.24 to 1.30× `voprf`'s time. Re-measure before and after on every AVX2 tier; keep s2n-bignum's path wherever it still wins, such as with AVX-512 IFMA.
- Constant time is the risk this takes on: add a ctgrind test for the new path, and differential tests against curve25519-dalek.
- Done: the constant-time multiplication runs dalek's AVX2 formulas on CPUs with AVX2 but without ADX. On an Arrow Lake core with ADX denied it measured 8 percent faster for blinding and 10 percent for evaluation (8 interleaved rounds); with ADX, at an earlier ungated checkpoint over 6 rounds, it measured 3.5 to 7 percent slower than s2n-bignum's, so ADX CPUs keep s2n-bignum's path.
- Left: the gap on ADX CPUs, which no AVX2 formula closes on Arrow Lake, where rind is already within 1.04 of `voprf`. Measure Zen and the cloud tiers the gap was recorded on; if s2n-bignum's path still trails `voprf` there with ADX, find why (Zen's MULX and ADX throughput) or close this quest.
- [The proof quest](/quest/m4/verified/ristretto255-avx2-mul.md) covers what now runs.

## Waiting

- Maintainer: the ADX-tier measurement on a Zen CPU (the owner's tests); check by re-running `oprf` with and without `RIND_CPU_DISABLE_adx` there.
