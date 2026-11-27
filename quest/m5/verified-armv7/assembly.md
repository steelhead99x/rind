# [XL] armv7's assembly is proven

## Goal

Every assembly routine armv7 runs is proven on the AArch32 model in `thirdparty/s2n-bignum/aarch32/`, so SHA-2, SHA-1, ChaCha20-Poly1305, AES and AES-GCM with the crypto extension, ML-KEM, and RSA earn the ✓ on armv7.

## Plan

Runs, each in `low/arm/`, in rough order of use:

- aws-lc's `sha_armv4`: SHA-256 and SHA-1 with the crypto extension, and SHA-256, SHA-1, and SHA-512 on NEON and without;
- aws-lc's `chacha-armv4` (integer below 192 bytes, NEON above) and its NEON Poly1305, under rind's port of `poly1305_arm.c`;
- aws-lc's `aesv8-armx` and `ghashv8-armx`, under rind's AES-GCM composition;
- OpenSSL's `keccak1600-armv4`, integer and NEON, under ML-KEM and SHA-3;
- OpenSSL's `ecp_nistz256-armv4` (`ecp_nistz256_mul_mont`, `_sqr_mont`, `_add`, and `_sub`), under P-256's field arithmetic and so its ECDH and ECDSA;
- aws-lc's `bn_mul8x_mont_neon` and `bn_mul_mont_nohw`, under RSA.

The model, which [its `RIND.md`](/thirdparty/s2n-bignum/RIND.md#rinds-aarch32-model) describes, decodes every integer, Advanced SIMD, and crypto-extension instruction of these routines as rind's release build for `armv7-unknown-linux-gnueabihf` emits them. When a routine changes, or a `.byte` or `.inst` spelling hides one, a word that no longer decodes gets no theorem, so its proof fails there: add the instruction to the model with cosimulation cases, in this quest's PR. A subroutine's theorem assumes `aarch32_bx_target` of its return address, aligned to four bytes for an A32 caller or with bit 0 set for a T32 one, so it holds for every armv7 target, as `proofs/hol-light/armv7/ct_compare_*.ml`'s do. `AARCH32_ADD_RETURN_NOSTACK_TAC` and `AARCH32_ADD_RETURN_STACK_TAC` take it from there, the second with `aligned 4` of SP too, counting a `vstmdb sp!, {d8-d15}` after the `push` in its prologue and naming Q4-Q7 in its `qreglist`, with `aarch32_nowrap` of its stack frame and of each buffer an access reaches that is more than one byte at an address not known aligned to four, such as a `VLD1.16` lane, or a transfer of more than one word, since a transfer that would run past 0xffffffff leaves the model. A conditional load or store records an access of no bytes when skipped, which `memaccess_inbounds` accepts only if the theorem lists a range of the access's kind, readable for a load and writable for a store, and whose length differs from a taken one's, so a condition that depends on a secret shows in the trace, as a branch's does. `admin/prove` writes each routine's bytes from rind's release build by its symbol without rind's version, as it does the compares'.

Route: prove each against the HOL Light or Lean specs the x86_64 and aarch64 quests write (FIPS 180-4, RFC 8439, FIPS 197 and SP 800-38D, FIPS 202, the Montgomery spec), and compose with the Rust proofs as on the other targets.
- Upstream: offering this work to awslabs/s2n-bignum is optional, and there is no standing approval: stop and ask the maintainer before posting there or anywhere outside [the orgs AGENTS.md lists](/AGENTS.md#development) (decided with the maintainer on 2026-11-07 on [kixel-ai/rind#448](https://github.com/kixel-ai/rind/pull/448)).
