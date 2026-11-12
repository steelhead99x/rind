# [M] AES and QUIC AES header protection are proven with AES hardware

## Goal

QUIC's AES-128 and AES-256 header protection, run on every packet of an AES-GCM connection, and the `cipher::Aes` block cipher behind it, earn the ✓ on x86_64 with AES-NI and on aarch64 with the crypto extension, AES-192 included.

## Plan

- Runs: `mid/aes.rs`'s `header_protection_mask` and `encrypt_block`, through `aead::quic`'s function-pointer dispatch, over rind's key expansion and block cipher: Graviola's AES-NI intrinsics on x86_64 (`low/x86_64/aes.rs`) and its NEON `aese`/`aesmc` intrinsics on aarch64 (`low/aarch64/aes.rs`), and their decryption schedules for `cipher::Aes`'s decryption.
- Already proven: x86_64's AES-NI key expansion and block cipher, inside the AES-GCM proof's key setup (`Rind/X86_64/AesKey.lean`, `AesNi.lean`), for AES-128 and AES-256 against Vale's AES spec.
- Route: Aeneas to Lean. On x86_64, reuse those lemmas, add AES-192 and the decryption schedule (`aesimc`, `aesdec`), and model the header-protection dispatch beside `Rind/X86_64/Dispatch.lean`'s ChaCha20 model. On aarch64, model `aese`, `aesd`, `aesmc`, and `aesimc` from the Arm manual as `Simd.lean` models Intel's, and prove the same theorems against FIPS 197.
- Also prove HKDF's `From<Okm>` conversion into an AES `aead::quic::HeaderProtectionKey` (`rind/src/high/hkdf.rs`), on top of the header-protection `new` this quest models, composing with the HKDF theorems as [moq-dev/rind#584](https://github.com/moq-dev/rind/pull/584) did for ChaCha20 header protection (maintainer, 2026-11-10: ✅ edit this quest; rejected: a separate quest). AES-128 and AES-256 only: no consumer derives an AES-192 key from HKDF, and Vale has no AES-192 routine.
- The tiers without AES hardware are [x86_64's](/quest/m5/verified/x86-no-aesni.md) and [aarch64's](/quest/m5/verified/aarch64-no-crypto.md) quests.
