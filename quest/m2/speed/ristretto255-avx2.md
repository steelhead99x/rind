# [M] ristretto255's variable-base multiplication runs curve25519-dalek's AVX2 formulas

## Goal

On x86_64 with AVX2, ristretto255's constant-time variable-base multiplication (OPRF blind and evaluate, VRF) runs curve25519-dalek's AVX2 field and point formulas, as Ed25519 verification without ADX already does, closing the 1.18 to 1.30× gap to RustCrypto's `voprf` that `benchmarks/gaps.toml`'s OPRF entry records.

## Plan

Decided 2026-11-18 (maintainer, [kixel-ai/rind#619](https://github.com/kixel-ai/rind/pull/619#issuecomment-6994276361)): ✅ keep this quest, ✅ worth the unproven constant-time port under the fastest-source rule (rejected: not until something calls OPRF or VRF on a hot path, planned in m4).

- Today `mid/ristretto255.rs`'s `Element::mul` runs a four-bit fixed window over s2n-bignum's field arithmetic. dalek's AVX2 backend is already ported in `low/x86_64/edwards25519_msm_avx2.rs` for Ed25519 verification, but that one is variable time over public scalars: this needs dalek's constant-time variable-base multiplication (`vartime` off: a fixed window with constant-time table selection), reusing the ported field and point layers.
- Measured on `nixos`, `ovh-iad`, and `ovh-sea` in the 0.4 report refresh: blinding 1.18 to 1.25× and evaluation 1.24 to 1.30× `voprf`'s time. Re-measure before and after on every AVX2 tier; keep s2n-bignum's path wherever it still wins, such as with AVX-512 IFMA.
- Constant time is the risk this takes on: add a ctgrind test for the new path, and differential tests against curve25519-dalek.
- The PR adds a proof quest under [the verified epic](/quest/m4/verified/README.md) for what then runs, reusing [the Ed25519 AVX2 proof](/quest/m4/verified/ed25519-avx2-verify.md)'s field and point lemmas.
