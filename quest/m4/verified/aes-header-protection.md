# [L] AES and QUIC AES header protection are proven on aarch64, AES-192 included

## Goal

QUIC's AES-128 and AES-256 header protection and the `cipher::Aes` block cipher behind it earn the ✓ on aarch64 with the crypto extension, `cipher::Aes`'s AES-192 is proven on x86_64 with AES-NI and on aarch64, and so are both targets' decryption schedules, which AES-CBC's decryption runs.

## Plan

- Land x86_64's AES-128 and AES-256 first (decided with the maintainer on 2026-11-12, from [moq-dev/rind#631](https://github.com/moq-dev/rind/pull/631)): ✅ land that partial step now (rejected: keep going in that PR until aarch64 and AES-192 are done), since the remaining work is independent of it.
- Already proven on x86_64 with AES-NI, in `Rind/X86_64/AesCipher.lean`: `cipher::Aes::new` and `encrypt_block`, AES header protection's `new` and `mask` through `Rind/X86_64/Dispatch.lean`'s model of the `aead::quic` statics, and HKDF's `From<Okm>` conversion to an AES header-protection key (`Rind/X86_64/HkdfAead.lean`), for AES-128 and AES-256, against Vale's FIPS 197 spec. `admin/prove` translates `mid::aes` on x86_64 and leaves it opaque on aarch64.
- aarch64: translate `mid::aes` there as on x86_64, model `low/aarch64/aes.rs`'s key expansion and block cipher by hand as `Rind/X86_64/AesNi.lean` models AES-NI's, and model the NEON intrinsics they call (`vaeseq_u8`, `vaesmcq_u8`, `vqtbl1q_u8`, `vextq_u8`, `vdupq_laneq_u32`, `vld1q_u8`, `vst1q_u8`, and the reinterpretations) from the Arm manual, as `Rind/X86_64/Simd.lean` models Intel's. Then prove the same theorems against Vale's spec, reusing `AesKey.lean`'s word-level schedule lemmas, and the HKDF conversion on aarch64.
- Test the NEON models on hardware, as `admin/simd-vectors.rs` tests the x86_64 ones: an aarch64 counterpart run in a `prove` workflow job on `ubuntu-24.04-arm`, which other workflows already use, since `admin/prove`'s job runs on x86_64.
- AES-192, on both targets: model `aes192_expand` and the generic `aes_block` (on x86_64 with `_mm_loadl_epi64`, `_mm_unpacklo_epi64`, and `_mm_alignr_epi8` added to `Simd.lean`), and prove the six-word schedule against Vale's `expandKey` at `nk = 6`. HKDF's conversion stays AES-128 and AES-256: no consumer derives an AES-192 key from HKDF.
- Decryption schedules, which only `AesDecKey`, and so AES-CBC's decryption, runs (`cipher::Aes` has no decryption): `invert_round_keys` and `hw_decrypt_block` on both targets, with `aesimc`, `aesdec`, and `aesdeclast` on x86_64 and `vaesimcq_u8` and `vaesdq_u8` on aarch64, against FIPS 197's equivalent inverse cipher, which Vale's spec lacks and this quest transliterates.
- The tiers without AES hardware are [x86_64's](/quest/m5/verified/x86-no-aesni.md) and [aarch64's](/quest/m5/verified/aarch64-no-crypto.md) quests.
