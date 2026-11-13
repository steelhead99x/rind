# [XL] AES-GCM on x86_64 with VAES is proven

## Goal

AES-GCM earns the ✓ on x86_64 CPUs with VAES and VPCLMULQDQ (Ice Lake and later, Zen 3 and later), the common tier on today's x86_64 servers and desktops: BoringSSL's VAES kernels, and rind's choice among them, Vale's, and its own, are proven.

## Plan

- Runs (`low/x86_64/aes_gcm_vaes.rs`): BoringSSL's `aes_gcm_{enc,dec}_update_vaes_avx2` from 256 bytes, and `aes_gcm_{enc,dec}_update_vaes_avx512` from 2 KB where the CPU has AVX-512, with their key-power setup `gcm_init_vpclmulqdq_avx2` and `_avx512` in BoringSSL's table layout; below those lengths, the [by-8 and by-16 intrinsics](/quest/m4/verified/aes-gcm-x86-intrinsics.md), and Vale's proven routines for opens under 256 bytes on cores without AVX-512.
- Already proven: Vale's routines, the AEAD API's glue on Vale's tier, and nothing of BoringSSL's. No published proof of a VAES or AVX-512 AES-GCM routine exists, and Vale has none.
- Route: HOL Light proofs of BoringSSL's four kernels and two key setups in s2n-bignum's x86_64 model, against s2n-bignum's SP 800-38D GCM spec (`common/gcm.ml`, which its aarch64 AES-GCM proofs use). The model decodes VPCLMULQDQ at VEX.256 and broad AVX2, but not VAES or EVEX: add VEX.256 `vaesenc` and `vaesenclast` for the AVX2 kernel, and AVX-512 for the other, building on [awslabs/s2n-bignum#462](https://github.com/awslabs/s2n-bignum/pull/462)'s EVEX decoding if it lands.
- The spec is moving: the draft [awslabs/s2n-bignum#490](https://github.com/awslabs/s2n-bignum/pull/490) rewrites `common/gcm.ml` and `common/fips197.ml` and adds known-answer tests for both (seen 2026-11-09). Build on the pin [the in-place quest](/quest/m4/verified/aes-gcm-aarch64-in-place.md) lands once #490 merges, not on today's `b4f17ee`.
- Then Aeneas to Lean for rind's glue around the kernels and the length-based choice, as `Rind/X86_64/AesGcm.lean` does for Vale's tier.
- The two GCM specs (maintainer, 2026-11-09): ✅ prove them equal in Lean (rejected: amend the composition rule to allow a spec-equivalence axiom; leave it for the quest to raise). This tier mixes kernels proven against s2n-bignum's `gcm_ae` and `gcm_ad` (`common/gcm.ml:166`, `:186` at rind's pin) with Vale's routines and the theorems of `Rind/X86_64/AesGcm.lean`, stated over Vale's `gcm_encrypt_LE` and `gcm_decrypt_LE`. So no axiom relates the two:
  - Transliterate both under the composition rule, as a function a proof must compute. Vale's `gcmEncrypt`, `gcmDecrypt`, and `computeIvBE` stop being opaque constants (`proofs/Rind/Vale.lean:238`, `:243`, `:249`) and become their `Vale.AES.GCM_s` definitions; [the intrinsics quest](/quest/m4/verified/aes-gcm-x86-intrinsics.md) already plans that for inputs of 2^32 bytes and more, so reuse its definitions if it made them. s2n-bignum's are its HOL Light definitions over `common/fips197.ml`'s AES.
  - `sbox` and `mixColumns` (`proofs/Rind/Vale.lean:89`, `:93`) become FIPS 197's definitions too, or the two specs' block ciphers cannot be shown to be one function.
  - One theorem each for encryption and decryption: for every key length both specs take (AES-192 once the intrinsics quest adds it to Vale's), 96-bit IV, AAD, and message within both specs' bounds, the two compute the same ciphertext and tag, and accept the same tags. Most of it is byte and bit order: Vale's little-endian `quad32` and reversed GF(2^128) elements against SP 800-38D's bit strings.
  - It goes in a file no target owns, beside `Rind/Vale.lean` and `Rind/Gf128.lean`, so every later quest that meets both specs imports it: [AES-GCM on aarch64](/quest/m4/verified/aes-gcm-aarch64.md) and [its AES-192 kernels](/quest/m4/verified/aes-gcm-aarch64-192.md), [aarch64 without the crypto extension](/quest/m5/verified/aarch64-no-crypto.md), and [x86_64 without AES-NI](/quest/m5/verified/x86-no-aesni.md). If one of those lands first, it writes the theorem there and this quest reuses it.
  - Size stays XL, the largest there is; the theorem adds to it.
- Do the AVX2 kernel first: it is the whole path on Zen 3 and on cores without AVX-512.
- Upstream: offering this work to awslabs/s2n-bignum is optional, and there is no standing approval: stop and ask the maintainer before posting there or anywhere outside the moq-dev and kixelated orgs (decided with the maintainer on 2026-11-07 on [kixel-ai/rind#448](https://github.com/kixel-ai/rind/pull/448)).

## Required

- [x86_64's by-8 and by-16 AES-GCM intrinsics are proven](/quest/m4/verified/aes-gcm-x86-intrinsics.md) - the short messages this tier hands to them
