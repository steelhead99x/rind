# [XL] armv7's assembly is proven

## Goal

Every assembly routine armv7 runs is proven on the AArch32 model in `thirdparty/s2n-bignum/aarch32/`, so AES and AES-GCM with the crypto extension, ML-KEM, RSA, and the constant-time compare earn the ✓ on armv7. SHA-1, SHA-2, ChaCha20, and Poly1305 are the portable bodies.

## Plan

Runs, each in `low/arm/`, in rough order of use:

- `generic::sha1`, `generic::sha256`, `generic::sha512` (the rolled loop), HACL*'s ChaCha20 rounds, and rind's 26-bit Poly1305. 32-bit Arm NEON and SHA intrinsics are unstable on the toolchain this crate builds with, so none of that is assembly;
- aws-lc's `aesv8-armx` and `ghashv8-armx`, under rind's AES-GCM composition;
- OpenSSL's `keccak1600-armv4`, integer and NEON, under ML-KEM and SHA-3;
- aws-lc's `bn_mul8x_mont_neon` and `bn_mul_mont_nohw`, under RSA;
- rind's constant-time compare, whose blocks `proofs/hol-light/armv7/ct_compare_*.ml` already prove where the target builds A32, leaving the axioms that restate them in armv7's Lean translation. `armv7-linux-androideabi` and the `thumbv7` targets build those `asm!` blocks as Thumb-2, and rustc refuses `#[instruction_set(arm::a32)]` on armv7's Linux and Android targets, while a naked function's symbol is Thumb there too. So move both compares into a `.code 32` `global_asm!`, as the other routines are, and prove them as functions once the model has `BX`, which covers every target's copy without a T32 model.

Route: prove each against the HOL Light or Lean specs the x86_64 and aarch64 quests write (FIPS 180-4, RFC 8439, FIPS 197 and SP 800-38D, FIPS 202, the Montgomery spec), and compose with the Rust proofs as on the other targets.
- Upstream: offering this work to awslabs/s2n-bignum is optional, and there is no standing approval: stop and ask the maintainer before posting there or anywhere outside [the orgs AGENTS.md lists](/AGENTS.md#development) (decided with the maintainer on 2026-11-07 on [kixel-ai/rind#448](https://github.com/kixel-ai/rind/pull/448)).

## Required

- [The AArch32 model covers armv7's integer assembly](/quest/m5/verified-armv7/model.md) - the integer instructions the proofs run on
- [The AArch32 model covers NEON and the crypto extension](/quest/m5/verified-armv7/model-neon.md) - the NEON and crypto-extension instructions the proofs run on
