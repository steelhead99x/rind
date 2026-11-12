# [L] The SHA-3 sponge is proven

## Goal

SHA3-256, SHA3-384, and SHA3-512 earn the ✓ on x86_64 and aarch64, and ML-KEM's SHAKE and SHA-3 calls rest on a proven sponge: rind's Rust sponge is proven against FIPS 202 down to s2n-bignum's Keccak-f routines, each already proven in HOL Light.

## Plan

- Runs: `mid/sha3.rs`, Graviola's sponge, about 670 lines (absorb, pad, squeeze, the SHAKE128 and SHAKE256 XOFs ML-KEM draws from, and the multi-state calls ML-KEM batches), over s2n-bignum's `sha3_keccak_f1600` (single state, with and without the SHA3 instructions on aarch64), `sha3_keccak2_f1600` and `sha3_keccak4_f1600` (two and four states), all proven.
- Route: Aeneas to Lean, with each Keccak-f routine an axiom under the composition rule, and FIPS 202 transliterated. SymCrypt's Aeneas-verified ML-KEM ([README-VERIFIEDCRYPTO.md](https://github.com/microsoft/SymCrypt/blob/c2e575ace0ea4b6b7a4184c1f19b81d1d5b2b5be/README-VERIFIEDCRYPTO.md)) proves its own SHA-3 in Lean; reuse its FIPS 202 spec if its license and shape fit, rather than writing a second one.
- x86_64's AVX-512 8-way Keccak is ML-KEM's sampler's, not the digest API's; [its own quest](/quest/m4/verified/mlkem-avx512-sampler.md) proves it.
