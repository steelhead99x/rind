# [M] rind imports pyca/verified-garbage's leakage contracts, and retires the harnesses they cover

## Goal

The SDE and QEMU trace harnesses of the VG routines whose leakage rind states as an axiom are retired, each once its wrapper keeps a trace check of its own, and VG's P-256 IFMA ECDH on x86_64 gets its leakage axiom too.
aarch64 SVE2 ChaCha20-Poly1305 (`Rind.Aarch64.VgChaCha20Poly1305Ct`) and x86_64 ML-KEM-768 (`Rind.X86_64.VgMlKem768Ct`) already state VG's `ConstantTime` of VG's own `Prog`, with `admin/vg-bytes --progs` binding that `Prog`'s printed text to VG's assembly and rind's bytes.
ML-KEM-768's is done: `mid::mlkem::ct_binsec_mlkem768_vg` checks its wrapper under BINSEC with each AVX-512 routine stubbed by its contract (`admin/ct-binsec`'s `CONTRACTS`), and `ct_sde_mlkem768` is gone.

- Each remaining wrapper gains a BINSEC region over its Rust the same way: the test forces the CPU check that picks the routine, as `cpu::force_avx512_for_vg_mlkem` does, and `CONTRACTS` lists the routine's outputs, which `admin/ct-binsec`'s BINSEC stub fills with fresh secrets, and the inputs its contract leaks, which the stub branches on; gdb's native run returns success without writing them. Next are the wrapper of `ct_sde_p256_ifma_ecdh` on x86_64 and of `ct_qemu_chacha20poly1305` on aarch64.
- Each SDE or QEMU harness is removed in the PR that lands its wrapper's region, never before, and TESTING.md's constant-time column cites the axiom and the region instead. `ct_qemu_chacha20poly1305` also traces VG's NEON seal and open, which the axioms do not cover (they state SVE2 only) and BINSEC cannot yet check: its PR retires only the SVE2 cases and keeps the NEON ones until a replacement covers that assembly. The aarch64 region needs `ubuntu-24.04-arm` or another aarch64 Linux host to run, since `admin/ct-binsec` runs the test natively under gdb.
- P-256 IFMA ECDH's leakage axiom lands by the same steps as the two done: vendor its `Impl/` closure, write its `Prog` as VG registers it, state `ConstantTime` of that `Prog`, and pin it in `Axioms.lean`.

## Plan

Follow-up from the 2026-11-18 /quest-plan on independence and Lean, which settled with the maintainer: ✅ once a routine's leakage contract is proven in Lean, its dedicated trace harness is retired, and ctgrind keeps running every test (rejected: keep every harness). Kept as a follow-up by the maintainer on 2026-11-18, on [kixel-ai/rind#893](https://github.com/kixel-ai/rind/pull/893): ✅ keep (rejected: drop).

- How each leakage axiom names the routine's code. Decided 2026-11-21 (maintainer, /quest-plan): ✅ VG's own `Prog`, from its vendored `Impl/` closure, with the link to rind's bytes resting on VG's vendored printer (rejected: rebuilding each `Prog` from VG's printed assembly with `Cosim/`'s parser; an opaque `Prog` constant per routine).
- The retained trace check for each wrapper whose SDE or QEMU harness retires. Decided 2026-11-21 (maintainer, /quest-plan): ✅ a BINSEC region over each wrapper's Rust, with the VG routine stubbed by its contract (rejected: adding AVX-512 and SVE2 decoders to BINSEC; ctgrind alone for the part of each wrapper valgrind runs; never retiring the harnesses). BINSEC decodes the wrappers' Rust but not VG's AVX-512 or SVE2 code, which the axiom covers instead.
- Retire a `ct_binsec_…` region only when it covers VG code alone.
- A contract's declared leakage must be public in rind's call too. Checked at VG `0aa40d6c`: ML-KEM-768's `leakRho` is `ρ`, which is in the encapsulation key; P-256 ECDH's `leak` is the peer's public key bytes; ChaCha20-Poly1305 open's `openLeak` is whether it returns 1, which rind returns. Recheck when the VG pin moves.
- The axioms need the cosimulation `admin/prove vg` runs for these instructions. The stack-slot model gap recorded in [the epic](/quest/m2/verified-garbage/README.md) holds back only the routines it holds back there.
