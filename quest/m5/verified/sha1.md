# [XL] SHA-1 is proven on every x86_64 and aarch64 tier

## Goal

SHA-1, and HMAC, HKDF, and PBKDF2 over it, earn the ✓ on every x86_64 and aarch64 tier, for the legacy APIs that still take it (RSA verification, OAEP, and HMAC).

## Plan

Runs, block function by tier, under padding and HMAC glue that `proofs/` already proves:

- x86_64 with SHA-NI, and with AVX2 without it: rind's intrinsics, `low/x86_64/sha1.rs`, and its finish pad on the SHA extensions. Route: Aeneas, with the SHA extensions' and AVX2 intrinsics modelled as `Rind/X86_64/Simd.lean` models AES-GCM's.
- x86_64 without AVX2: aws-lc's `sha1_block_data_order_avx` on Intel, `_ssse3` elsewhere, and `_nohw` without SSSE3. Route: HOL Light in s2n-bignum's x86_64 model against a FIPS 180-4 SHA-1 spec, beside [awslabs/s2n-bignum#450](https://github.com/awslabs/s2n-bignum/pull/450)'s SHA-256.
- aarch64 with the crypto extension: rind's intrinsics, `low/aarch64/sha1.rs`. Route: Aeneas, modelling `sha1c`, `sha1p`, `sha1m`, `sha1h`, `sha1su0`, and `sha1su1` from the Arm manual.
- aarch64 without it: aws-lc's `sha1_block_data_order_nohw`. Route: HOL Light in s2n-bignum's aarch64 model.

Each enters as the `ShaBlocks` hypothesis's SHA-1 half does today, which this retires.
- Upstream: offering this work to awslabs/s2n-bignum is optional, and there is no standing approval: stop and ask the maintainer before posting there or anywhere outside the moq-dev and kixelated orgs (decided with the maintainer on 2026-11-07 on [kixel-ai/rind#448](https://github.com/kixel-ai/rind/pull/448)).
