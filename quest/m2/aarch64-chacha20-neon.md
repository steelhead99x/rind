# [S] aarch64's ChaCha20 cipher takes Graviola's faster NEON layout

## Goal

On aarch64, the bare ChaCha20 stream cipher (`mid/chacha20.rs`, which DTLS 1.3 record number protection uses) runs Graviola's `bdad1050` NEON layout (2026-10-23, "Additional speedup for ChaCha20 on some aarch64 implementations") if it measures faster than rind's current routine, which began as Graviola's from cifra, on the aarch64 report hosts; otherwise this quest records the numbers and is deleted.

## Plan

Found by the 2026-11-14 [upstream-updates](/quest/m2/upstream-updates.md) run. Graviola measures about 25% faster on Graviton 2 and 5% on Apple M4. rind's ChaCha20-Poly1305 on aarch64 runs aws-lc's NEON code and is unaffected; only the bare cipher, through `low/aarch64/chacha20.rs`, gains.

- pyca/verified-garbage's routines now run most lengths ([kixel-ai/rind#882](https://github.com/kixel-ai/rind/pull/882)): from 128 bytes with SVE2, and without it from 192 to 256 bytes and from 448. A port gains only below those and from 257 to 447 bytes without SVE2, where VG's NEON routine lost to rind's code, so measure there, and re-time `low/aarch64/chacha20.rs`'s thresholds against the port, since a faster rind loop moves them.
- Bench `rind-bench`'s ChaCha20 against aws-lc-rs before and after on each aarch64 host available.
- [ChaCha20-Poly1305 is proven on aarch64](/quest/m4/verified/chacha20-poly1305-aarch64.md) plans to prove this routine; a port changes what it proves.

## Related

- [ChaCha20-Poly1305 is proven on aarch64](/quest/m4/verified/chacha20-poly1305-aarch64.md) - proves the routine this replaces
