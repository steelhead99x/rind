# [S] ChaCha20-Poly1305 on Intel without AVX-512 runs verified-garbage's code where it is faster

## Goal

On Intel CPUs with AVX2 but no AVX-512, such as `desktop`'s Arrow Lake, ChaCha20-Poly1305 seal and open run whichever of pyca/verified-garbage's code and aws-lc's one-pass `chacha20_poly1305_x86_64`, which rind runs today, is faster at each length, measured under rind's glue at every AEAD size the speed bar sets.

## Plan

Found by `desktop`'s first held run ([kixel-ai/rind#1103](https://github.com/kixel-ai/rind/pull/1103); 2.01 other CPUs busy against a limit of 2.4). Kept 2026-11-27 (maintainer) ✅ (rejected: drop it).

- VG's API took 0.88 of rind's time to seal 16 KB (3.63 against 4.11 µs) and 0.97 at 1350 B (422 against 437 ns); aws-lc-rs and ring matched rind (4.12 and 4.11 µs). On AMD without AVX-512 (`nixos`'s Zen 3) the two were level at every size, and Zen 4 and 5 run VG's IFMA routines already.
- First find which VG routines its API runs on this CPU, which has AVX2 and AVX-VNNI but neither AVX-512 nor AVX-IFMA: `vg_chacha20_apply_avx2` and a separate Poly1305 pass are the likely pair. Then time them under rind's glue against aws-lc's routine on `desktop`, seal and open, at every AEAD size.
- Found 2026-11-28: on this CPU VG's API runs `vg_chacha20_poly1305_seal_avx2` and `vg_chacha20_poly1305_open_avx2` (features AVX and AVX2). The seal calls `vg_chacha20_poly1305_seal_body_avx2`, which past VG's `fold` stitches AVX2 ChaCha20 with AVX2 Poly1305 in 512-byte passes; the open calls `vg_chacha20_xor_avx2`, then `vg_poly1305_blocks_avx2` (VG's `Impl/ChaCha20Poly1305/X86_64.lean`). Both enter Intel's MXCSR mitigation themselves, as the IFMA pair does. The branch `claude/q-arrow-lake-vg-chacha20-poly1305` imports them and runs them behind `HaveVgChaCha20Poly1305::check_seal` and `check_open` on Intel without AVX-512, from `cpu::INTEL_AVX2_SEAL_FROM` and `INTEL_AVX2_OPEN_FROM` (1024 bytes for now), under the IFMA pair's wrapper and Lean axioms. What remains is `desktop`'s timing of both codes under rind's glue, built with `--cfg rind_cpu_disable`, with `RIND_CPU_DISABLE_intel=1` for aws-lc's, at every AEAD size and around the crossover, and setting the two limits from it.
- Switch only where they win at every size, or by length if the crossover is clean, picking by vendor as `rind/src/low/x86_64/sha512.rs` does with `is_intel`, so AMD keeps its measured choice, as [kixel-ai/rind#1108](https://github.com/kixel-ai/rind/pull/1108) settled it on Zen 4. If VG wins nowhere under rind's glue, record the numbers in the PR, turn `benchmarks/gaps.toml`'s `desktop` ChaCha20-Poly1305 entry into a reason, and delete this quest.

## Hosts

- linux - `desktop` is the only Intel host without AVX-512
