# [XS] Apple's DIT takes effect before rind's constant-time code runs

## Goal

On Apple silicon, the instructions after rind sets DIT cannot run speculatively without it, as Apple's guidance asks.

## Plan

Found on 2026-11-12, reading pyca/verified-garbage's README, which says Apple asks for a speculation barrier after setting DIT. Decided with the maintainer the same day: ✅ a quest in m2.

- `rind/src/low/aarch64/cpu.rs`'s `dit` module writes `msr DIT, #1` with no barrier after it.
- Confirm the requirement in Apple's own documentation, "Writing ARM64 code for Apple platforms", before changing anything, and check what aws-lc does when it sets DIT.
- If confirmed, add the barrier Apple names, `sb` where the CPU has FEAT_SB (`hw.optional.arm.FEAT_SB`) and `dsb nsh` then `isb sy` otherwise, and measure its cost on `kixtop`.
