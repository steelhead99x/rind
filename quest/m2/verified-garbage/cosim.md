# [L] VG's ISA models are cosimulated for the instructions rind runs

## Goal

Every instruction in the VG routines rind switches to is checked against the CPU by random-instruction cosimulation on VG's Lean model, and the bytes rind vendors decode to the assembly text VG's proofs are about. A ✓ can then rest on VG's theorems.

## Plan

- VG's models (`lean/VerifiedGarbage/TCB/<ISA>/`) import only Lean core and are executable. Vendor the ones the switched routines need into `proofs/` at the pinned VG commit, with the `Spec/` modules their theorems state.
- Run each instruction on random inputs on the CPU and in the model, as `admin/prove cosim` runs the s2n-bignum fork's `x86/proofs/rind_cosim.ml` for rind's additions. x86_64 runs in CI; aarch64 needs an aarch64 runner.
- VG emits straight-line code as base64 machine code and the rest as assembly text. Decode the vendored blobs and check them against VG's `assembly/*.s` for the pinned commit, since VG's CI only checks its encoder against golden tests.
- A model fault the cosimulation finds is reported to VG with a reproducer once the maintainer approves posting there, and blocks the ✓ for every routine that uses the instruction.
- Scope: the instructions [the measurement](/quest/m2/verified-garbage/bench.md)'s switch quests use. A switch landed later extends the cosimulation in its own ✓ quest.

## Required

- [VG measured](/quest/m2/verified-garbage/bench.md) - which routines rind switches to, and so which instructions to cosimulate
