# [L] AES-CTR, AES-CBC, and AES key wrap are proven with AES hardware

## Goal

`cipher::AesCtr`, AES-CBC, and `key_wrap::AesKek` (RFC 3394 and RFC 5649) earn the ✓ on x86_64 with AES-NI and on aarch64 with the crypto extension.

## Plan

- Runs on x86_64: aws-lc's `aes_hw_ctr32_encrypt_blocks` and `aes_hw_cbc_encrypt` assembly under `low/generic/ctr.rs` and rind's Rust; on aarch64, rind's NEON CTR by 8 (`low/aarch64/aes_ctr.rs`) and CBC (`aes_cbc.rs`) intrinsics; and on both, `mid/aes_kw.rs`'s wrap and unwrap over the block cipher.
- Route: on x86_64, HOL Light proofs of the two aws-lc routines in s2n-bignum's x86_64 model, which has an AES-NI model, against FIPS 197 and SP 800-38A; on aarch64, Aeneas over `Rind/Aarch64/Neon.lean`'s intrinsic models, reusing `Rind/Aarch64/AesKey.lean`'s block cipher and decryption proofs, the latter against `Rind/AesInverse.lean`'s equivalent inverse cipher; and the counter wrapping, CBC chaining, and key wrap in Lean against SP 800-38A and SP 800-38F.
- Upstream: offering this work to awslabs/s2n-bignum is optional, and there is no standing approval: stop and ask the maintainer before posting there or anywhere outside [the orgs AGENTS.md lists](/AGENTS.md#development) (decided with the maintainer on 2026-11-07 on [kixel-ai/rind#448](https://github.com/kixel-ai/rind/pull/448)).
