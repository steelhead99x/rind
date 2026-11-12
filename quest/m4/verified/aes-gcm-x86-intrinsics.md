# [L] x86_64's by-8 and by-16 AES-GCM intrinsics are proven

## Goal

rind's own AES-GCM kernels on x86_64, the by-8 AES-CTR and GHASH and the AVX-512 by-16, are proven, so AES-GCM earns the ✓ on x86_64 CPUs with AES-NI but without AVX, and every input the Vale tier hands to them is covered: seals under 129 bytes, AAD or messages of 2^32 bytes and more, AES-192, IVs other than 96 bits, and truncated tags.

## Plan

- Runs: `low/x86_64/aes_gcm.rs`, Graviola's stitched by-8 AES-CTR and by-8 GHASH in SSE-encoded intrinsics, its optional AVX-512 by-16 AES-CTR and GHASH, rind's GHASH key powers, counter, partial blocks, J0 for other IV lengths, and the tag check, under the AEAD API's glue that `proofs/` already proves for Vale's tier.
- Already proven: the AES-NI key expansion and block cipher and the PCLMULQDQ GHASH key powers (`Rind/X86_64/AesKey.lean`, `Ghash.lean`, `Gf128.lean`), the partial-block loads and stores (`PartialBlock.lean`), and the AEAD dispatch model, against Vale's AES and GF(2^128) specs.
- Route: Aeneas to Lean, extending `Rind/X86_64/Simd.lean`'s intrinsic models with what the kernels call (`aesenc`, `aesenclast`, `pclmulqdq`, shuffles, and the AVX-512 forms for by-16), against the same `gcm_encrypt_LE` and `gcm_decrypt_LE` specs, adding AES-192 to the AES spec.
- The Vale tier runs by-8 for AAD or messages of 2^32 bytes and more, since Vale's routines take neither in chunks: each starts GHASH from zero ([`Gcm_blocks_auth`](https://github.com/hacl-star/hacl-star/blob/f557259007db9933442dde10aa995c1b00bd3446/vale/code/crypto/aes/x64/Vale.AES.X64.GCMencryptOpt.vaf#L696)) and requires its counter block to be `compute_iv_BE` of an IV ([`Gcm_blocks_stdcall`](https://github.com/hacl-star/hacl-star/blob/f557259007db9933442dde10aa995c1b00bd3446/vale/code/crypto/aes/x64/Vale.AES.X64.GCMencryptOpt.vaf#L1722)), and the decrypting one returns only whether the tag matches. Vale's `gcm_encrypt_LE` and `gcm_decrypt_LE` require both lengths under 2^32 ([GCM_s](https://github.com/hacl-star/hacl-star/blob/f557259007db9933442dde10aa995c1b00bd3446/vale/specs/crypto/Vale.AES.GCM_s.fst#L39)), so covering longer ones means transliterating them without that bound, as the composition rule allows for a function a proof must compute.
- This quest owns `aead::gcm::Key`'s other IV lengths and truncated tags, which run `encrypt_any` and `decrypt_any` (`rind/src/mid/aes_gcm.rs`) on these kernels (maintainer, 2026-11-09: ✅ here; rejected: in m3's Vale-tier quest, which kept only the 12-byte, full-tag glue).
- The VAES tier's short messages run these kernels too; [its quest](/quest/m4/verified/aes-gcm-x86-vaes.md) composes them with BoringSSL's.
