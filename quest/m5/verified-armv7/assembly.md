# [XL] armv7's assembly is proven

## Goal

Every assembly routine armv7 runs is proven on [the AArch32 model](/quest/m5/verified-armv7/model.md), so SHA-2, SHA-1, ChaCha20-Poly1305, AES and AES-GCM with the crypto extension, ML-KEM, RSA, and the constant-time compare earn the ✓ on armv7.

## Plan

Runs, each in `low/arm/`, in rough order of use:

- aws-lc's `sha_armv4`: SHA-256 and SHA-1 with the crypto extension, and SHA-256, SHA-1, and SHA-512 on NEON and without;
- aws-lc's `chacha-armv4` (integer below 192 bytes, NEON above) and its NEON Poly1305, under rind's port of `poly1305_arm.c`;
- aws-lc's `aesv8-armx` and `ghashv8-armx`, under rind's AES-GCM composition;
- OpenSSL's `keccak1600-armv4`, integer and NEON, under ML-KEM and SHA-3;
- aws-lc's `bn_mul8x_mont_neon` and `bn_mul_mont_nohw`, under RSA;
- rind's constant-time compare.

Route: prove each against the HOL Light or Lean specs the x86_64 and aarch64 quests write (FIPS 180-4, RFC 8439, FIPS 197 and SP 800-38D, FIPS 202, the Montgomery spec), and compose with the Rust proofs as on the other targets.
- Upstream: offering this work to awslabs/s2n-bignum is optional, and there is no standing approval: stop and ask the maintainer before posting there or anywhere outside the moq-dev and kixelated orgs (decided with the maintainer on 2026-11-07 on [kixel-ai/rind#448](https://github.com/kixel-ai/rind/pull/448)).

## Required

- [An AArch32 instruction model checks armv7's assembly](/quest/m5/verified-armv7/model.md) - the model the proofs run on
- [armv7 runs the Rust proofs](/quest/m5/verified-armv7/prove.md) - the armv7 translation these routines' theorems compose with
- [x86_64 SHA-512 on AVX2 is proven](/quest/m4/verified/sha512-x86-avx2.md) - the pinned FIPS 180-4 SHA-512 spec and its Lean axiom shape
