# [XL] armv7's assembly is proven

## Goal

Every assembly routine armv7 runs is proven on the AArch32 model in `thirdparty/s2n-bignum/aarch32/`, so SHA-2, SHA-1, ChaCha20-Poly1305, AES and AES-GCM with the crypto extension, ML-KEM, RSA, and the constant-time compare earn the ✓ on armv7.

## Plan

Runs, each in `low/arm/`, in rough order of use:

- aws-lc's `sha_armv4`: SHA-256 and SHA-1 with the crypto extension, and SHA-256, SHA-1, and SHA-512 on NEON and without;
- aws-lc's `chacha-armv4` (integer below 192 bytes, NEON above) and its NEON Poly1305, under rind's port of `poly1305_arm.c`;
- aws-lc's `aesv8-armx` and `ghashv8-armx`, under rind's AES-GCM composition;
- OpenSSL's `keccak1600-armv4`, integer and NEON, under ML-KEM and SHA-3;
- aws-lc's `bn_mul8x_mont_neon` and `bn_mul_mont_nohw`, under RSA;
- rind's constant-time compare, whose blocks `proofs/hol-light/armv7/ct_compare_*.ml` already prove where the target builds A32, leaving the axioms that restate them in armv7's Lean translation. `armv7-linux-androideabi` and the `thumbv7` targets build those `asm!` blocks as Thumb-2, and rustc refuses `#[instruction_set(arm::a32)]` on armv7's Linux and Android targets, while a naked function's symbol is Thumb there too. So move both compares into a `.code 32` `global_asm!`, as the other routines are, and prove them as functions, which covers every target's copy of their instructions without a T32 model.

The model, which [its `RIND.md`](/thirdparty/s2n-bignum/RIND.md#rinds-aarch32-model) describes, decodes every integer instruction of these routines as rind's release build for `armv7-unknown-linux-gnueabihf` emits them. When a routine changes, or a `.byte` or `.inst` spelling hides one, a word that no longer decodes gets no theorem, so its proof fails there: add the instruction to the model with cosimulation cases, in this quest's PR. A subroutine's theorem assumes `aligned 4` of its return address, which `AARCH32_ADD_RETURN_NOSTACK_TAC` and `AARCH32_ADD_RETURN_STACK_TAC` take from it, and the second of SP too, with `aarch32_nowrap` of its stack frame and of each buffer an unaligned word or a transfer of more than one word reaches, since a transfer that would run past 0xffffffff leaves the model. A conditional load or store records an access of no bytes when skipped, which `memaccess_inbounds` accepts only if the theorem lists a range of the access's kind, readable for a load and writable for a store, and whose length differs from a taken one's, so a condition that depends on a secret shows in the trace, as a branch's does. That is an A32 caller's return address. `armv7-linux-androideabi` and the `thumbv7` targets call these routines from Thumb-2 code, whose return address has bit 0 set, so the return leaves the model there and the subroutine theorem says nothing of that caller: only the core theorem holds for it, which covers the routine from its own entry to its own exit, without the stack wrapper's push, the pop that restores it, or the return. So give the model's state the T bit, so that `BX` and a load into PC of such a target step to it with the bit set, and state each subroutine theorem for either caller; that is one flag and no T32 instruction. Decided 2026-11-24 (maintainer, /quest-run, on [kixel-ai/rind#1000](https://github.com/kixel-ai/rind/pull/1000)): ✅ model the T bit (rejected: core theorems alone on Thumb targets).

Route: prove each against the HOL Light or Lean specs the x86_64 and aarch64 quests write (FIPS 180-4, RFC 8439, FIPS 197 and SP 800-38D, FIPS 202, the Montgomery spec), and compose with the Rust proofs as on the other targets.
- Upstream: offering this work to awslabs/s2n-bignum is optional, and there is no standing approval: stop and ask the maintainer before posting there or anywhere outside [the orgs AGENTS.md lists](/AGENTS.md#development) (decided with the maintainer on 2026-11-07 on [kixel-ai/rind#448](https://github.com/kixel-ai/rind/pull/448)).

## Required

- [The AArch32 model covers NEON and the crypto extension](/quest/m5/verified-armv7/model-neon.md) - the NEON and crypto-extension instructions the proofs run on
