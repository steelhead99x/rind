# [S] ChaCha20-Poly1305 on Intel without AVX-512 runs verified-garbage's code where it is faster

## Goal

On Intel CPUs with AVX2 but no AVX-512, such as `desktop`'s Arrow Lake, ChaCha20-Poly1305 seal and open run whichever of pyca/verified-garbage's code and aws-lc's one-pass `chacha20_poly1305_x86_64`, which rind runs today, is faster at each length, measured under rind's glue at every AEAD size the speed bar sets.

## Plan

Found by `desktop`'s first held run ([kixel-ai/rind#1103](https://github.com/kixel-ai/rind/pull/1103); 2.01 other CPUs busy against a limit of 2.4). Kept 2026-11-27 (maintainer) ✅ (rejected: drop it).

- VG's API took 0.88 of rind's time to seal 16 KB (3.63 against 4.11 µs) and 0.97 at 1350 B (422 against 437 ns); aws-lc-rs and ring matched rind (4.12 and 4.11 µs). On AMD without AVX-512 (`nixos`'s Zen 3) the two were level at every size, and Zen 4 and 5 run VG's IFMA routines already.
- First find which VG routines its API runs on this CPU, which has AVX2 and AVX-VNNI but neither AVX-512 nor AVX-IFMA: `vg_chacha20_apply_avx2` and a separate Poly1305 pass are the likely pair. Then time them under rind's glue against aws-lc's routine on `desktop`, seal and open, at every AEAD size.
- Switch only where they win at every size, or by length if the crossover is clean, picking by vendor as `rind/src/low/x86_64/sha512.rs` does with `is_intel`, so AMD keeps its measured choice, as [kixel-ai/rind#1108](https://github.com/kixel-ai/rind/pull/1108) settled it on Zen 4. If VG wins nowhere under rind's glue, record the numbers in the PR, turn `benchmarks/gaps.toml`'s `desktop` ChaCha20-Poly1305 entry into a reason, and delete this quest.

## Hosts

- linux - `desktop` is the only Intel host without AVX-512
