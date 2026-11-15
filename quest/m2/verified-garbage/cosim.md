# [L] VG's ISA models are cosimulated for the instructions rind runs

## Goal

Every instruction in the VG routines rind switches to is checked against the CPU by random-instruction cosimulation on VG's Lean model, and the bytes rind vendors decode to the assembly text VG's proofs are about. A ✓ can then rest on VG's theorems.

## Plan

- VG's models (`lean/VerifiedGarbage/TCB/<ISA>/`) import only Lean core and are executable. Vendor the ones the switched routines need into `proofs/` at the pinned VG commit, with the `Spec/` modules their theorems state.
- Run each instruction on random inputs on the CPU and in the model, as `admin/prove cosim` runs the s2n-bignum fork's `x86/proofs/rind_cosim.ml` for rind's additions. x86_64 runs in CI; aarch64 needs an aarch64 runner.
- VG emits straight-line code as base64 machine code and the rest as assembly text. Decode the vendored blobs and check them against VG's `assembly/*.s` for the pinned commit, since VG's CI only checks its encoder against golden tests.
- A model fault the cosimulation finds is reported to VG with a reproducer once the maintainer approves posting there, and blocks the ✓ for every routine that uses the instruction.
- Scope: the x86_64 and aarch64 instructions of the VG routines the epic's switch quests name (P-256, P-384, X25519 and Ed25519 on AVX-512, ML-KEM-768, SHA-3, aarch64 ChaCha20-Poly1305, RSA on AVX-512, aarch64 PBKDF2, ML-DSA signing without AVX2, and AES-128 header protection), at the pinned VG commit; `cipher::ChaCha20`'s switch, measured later, extends it in its own ✓ quest. A switch that adds routines later extends the cosimulation in its own ✓ quest.
