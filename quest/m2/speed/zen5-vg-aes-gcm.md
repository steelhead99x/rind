# [S] AES-GCM on Zen 5 runs verified-garbage's AVX-512 kernels where they are faster

## Goal

On Zen 5, AES-GCM seal and open run whichever of pyca/verified-garbage's prepared AVX-512 kernels and BoringSSL's `aes-gcm-avx512-x86_64`, which rind runs today, is faster at each length, measured under rind's glue at every AEAD size the speed bar sets, without slowing key setup.

## Plan

Found by the 0.4 report refresh ([kixel-ai/rind#991](https://github.com/kixel-ai/rind/pull/991)), the first quiet run on `fedora` (Ryzen 9 9950X, 2.5 other CPUs busy against a limit of 3.2).

- VG's API took 0.82 of rind's time to open 16 KB with AES-128 (495 against 602 ns), 0.89 to seal it (452 against 510), 0.90 and 0.93 with AES-256, and 0.89 to seal 1350 B with AES-256 (93 against 105). It lost at 32 B everywhere (33 against 26 ns) and to open 1350 B (107 against 86).
- [kixel-ai/rind#955](https://github.com/kixel-ai/rind/pull/955) ran these kernels, `vg_aes_gcm_{seal,open}_prepared_vaes_vpclmul_avx512`, under rind's glue on the weekly bench's Xeon 6975P runners and kept rind's code: they took 1.08 to 1.77 of rind's time below 8 KB, and only AES-128 and AES-192 from 12 KB came out ahead. Building VG's key-power table also raised rind's key setup to 257 to 274 ns, against aws-lc-rs's 95 to 132. Zen 5 was never measured under rind's glue, and `fedora`'s runs at the time were too noisy to settle it.
- Rerun #955's comparison on `fedora` (its branch or a fresh vendoring with `admin/import-vg`), seal and open, every key size and AEAD size. If VG wins only on long messages, a switch must reuse rind's key powers or build VG's lazily, since key setup is on QUIC's hot path. If it wins nowhere under rind's glue, record the numbers in the PR, turn `benchmarks/gaps.toml`'s `fedora` AES-GCM entry into a reason, and delete this quest.
- A switch that picks by CPU family keeps Zen 4 and Intel on their measured choice, as [the Zen 4 ChaCha20-Poly1305 quest](/quest/m2/speed/zen4-vg-chacha20-poly1305.md) does for its AEAD.

## Hosts

- linux - `fedora` is the only Zen 5 host
