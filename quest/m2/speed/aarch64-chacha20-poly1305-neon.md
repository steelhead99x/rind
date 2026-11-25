# [S] aarch64 ChaCha20-Poly1305 without SVE2 runs verified-garbage's NEON one pass where it is faster

## Goal

On aarch64 cores without SVE2, such as Apple's, ChaCha20-Poly1305 and XChaCha20-Poly1305 seal and open run pyca/verified-garbage's `vg_chacha20_poly1305_{seal,open}_neon` at every length where it measures faster than aws-lc's NEON code, which rind runs there today, and aws-lc's at the rest.

## Plan

Found by the 0.4 report refresh ([kixel-ai/rind#991](https://github.com/kixel-ai/rind/pull/991)) at `3f76a53f`.

- `kixtop` (Apple M4) sealed 16 KB in 5.51 µs with VG's API against rind's 8.08 (1.47×), was level at 1350 B (757 against 763 ns), and lost at 32 B (195 against 150 ns). The weekly bench's `no SHA-3` tier, a Neoverse N2 with SVE2 denied, agrees ([run 44941104585](https://github.com/kixel-ai/rind/actions/runs/44941104585)): VG 12.6 against rind's 14.2 µs at 16 KB, 1395 against 1429 ns at 1350 B, and 279 against 235 ns at 32 B.
- [kixel-ai/rind#813](https://github.com/kixel-ai/rind/pull/813) took VG's SVE2 one pass but kept aws-lc's code without SVE2, since VG's NEON routines took up to 1.06 of its time at 32 to 512 bytes on the M4; it never split by length. rind already runs VG's NEON ChaCha20 above a length threshold ([kixel-ai/rind#882](https://github.com/kixel-ai/rind/pull/882)), and this takes the same shape: vendor the NEON seal and open with `admin/import-vg` at its pin, and pick by length in `low/aarch64/chacha20poly1305.rs`, the threshold set where both measure level on the M4 and the N2, seal and open alike, at every AEAD size the speed bar sets.
- Behavior and wipes as the [VG epic](/quest/m2/verified-garbage/README.md) sets out; add the routines to `admin/prove vg`'s cosimulation and a ctgrind row, and update ALGORITHMS.md's aarch64 row and [the aarch64 ChaCha20-Poly1305 proof quest](/quest/m4/verified/chacha20-poly1305-aarch64.md), whose code this changes.
- Bench `chacha20_poly1305` on the weekly bench's aarch64 tiers and `kixtop` before and after; if VG loses at every length once under rind's glue, record the numbers in the PR and delete this quest with `benchmarks/gaps.toml`'s entry turned into a reason.
