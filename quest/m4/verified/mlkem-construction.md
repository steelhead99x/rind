# [XL] ML-KEM-768's construction is proven

## Goal

ML-KEM-768 key generation, encapsulation, and decapsulation earn the ✓ on aarch64 and on x86_64 with AVX2 (without the AVX-512 sampler, which [its own quest](/quest/m4/verified/mlkem-avx512-sampler.md) adds): rind's FIPS 203 construction is proven down to s2n-bignum's and mlkem-native's proven polynomial routines and the proven sponge, whose theorems (`shake128x4_squeeze_spec`, `shake256_batch_spec`, `squeezing_squeeze_spec`, and the SHA-3 contexts') `proofs/Rind/X86_64/Sha3.lean` states. rind-rustls's default key exchange, X25519MLKEM768, then earns it wherever X25519 has it.

## Plan

- Runs: `mid/mlkem.rs` and `mid/mlkem/sample_ntt.rs` (about 1,000 lines: K-PKE, the Fujisaki-Okamoto transform with its constant-time compare and select, CBD sampling, SampleNTT's driver, encapsulation-key checks), `low/generic/mlkem.rs`, and the Rust byte encoding and decompression on aarch64 (frombytes, compress), over s2n-bignum's NTT, inverse NTT, base multiplication, mulcache, reduce, tomont, tobytes, frombytes, unpack, and rejection sampling, and on x86_64 mlkem-native's AVX2 compression, all proven in HOL Light.
- Route: Aeneas to Lean against FIPS 203, each routine an axiom under the composition rule. Their HOL Light statements are over mlkem-native's coefficient order and Montgomery form, so the Lean side needs the bridge lemmas.
- SymCrypt's Aeneas-verified Rust ML-KEM ([README-VERIFIEDCRYPTO.md](https://github.com/microsoft/SymCrypt/blob/c2e575ace0ea4b6b7a4184c1f19b81d1d5b2b5be/README-VERIFIEDCRYPTO.md)) proves the same construction in Lean, about 38,000 lines for 2,125 of Rust. Reuse its FIPS 203 spec and lemmas where its license and shape fit.
- The constant tables (zetas) the routines' proofs assume are rind's; prove them as `Rind/Aarch64/P256Table.lean` proves P-256's generator table.
