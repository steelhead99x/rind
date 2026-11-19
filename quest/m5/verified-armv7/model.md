# [L] The AArch32 model covers armv7's integer assembly

## Goal

The AArch32 model in `thirdparty/s2n-bignum/aarch32/` decodes, and cosimulates against qemu-arm, every A32 integer instruction armv7's assembly in `low/arm/` runs, so [armv7's assembly](/quest/m5/verified-armv7/assembly.md) can prove its integer routines on it.

## Plan

- Route (maintainer, 2026-11-12, on [kixel-ai/rind#663](https://github.com/kixel-ai/rind/pull/663)): ✅ HOL Light in s2n-bignum's style (rejected: Lean generated from Arm's Sail model).
- The model follows s2n-bignum's RV32IM model. It already holds data processing with an immediate shift or a modified immediate, `MOVW` and `MOVT`, immediate-offset `LDR`, `LDRB`, `STR`, and `STRB`, and `B`, each under any condition; `aarch32/proofs/simulator.ml` cosimulates them, and `proofs/hol-light/armv7/ct_compare_*.ml` prove rind's compares on them.
- Add what a scan of `low/arm/{aws_lc,boringssl,openssl}/*.s` finds the integer paths use: register-shifted register operands, PC as an operand (`adr`, literal `ldr`), register-offset loads and stores, `LDM` and `STM` with write-back (`push` and `pop` among them), `LDRD` and `STRD`, `BL` and `BX`, `MUL`, `UMULL`, and `UMLAL`, `REV`, `DMB`, and `NOP` (`neg` is `RSB` from zero, already there). Rescan when a routine lands, since `.byte` and `.inst` spellings hide instructions from a mnemonic search.
- Thumb stays out: every `global_asm!` that includes these sources sets `.code 32`, so they are A32 on every target, Android's included, and their `it` instructions assemble to nothing. Only Rust follows a target's default, Thumb-2 on `armv7-linux-androideabi` and the `thumbv7` targets, which leaves the compares' inline `asm!` T32 there; [armv7's assembly](/quest/m5/verified-armv7/assembly.md) moves them into A32 rather than this model gaining T32. `BX` to an address with bit 0 set would enter Thumb, so the model refuses it rather than step into a state it cannot represent.
- Each added form gets cosimulation cases, the multi-register memory forms through SP into the executor's scratch buffer, as the single loads and stores do now.
- Add the AAPCS subroutine wrappers s2n-bignum's other models have, such as `ARM_ADD_RETURN_NOSTACK_TAC`'s, once a routine ends in `bx lr`.
- Offering the model to awslabs/s2n-bignum is [upstream-reports](/quest/m2/upstream-reports.md)'s, with the fork's other changes, and needs the maintainer's approval first, as any post outside [the orgs AGENTS.md lists](/AGENTS.md#development) does.
