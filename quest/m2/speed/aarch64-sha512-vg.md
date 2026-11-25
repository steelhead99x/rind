# [S] aarch64 SHA-512 with the SHA-512 instructions runs verified-garbage's block function where it is faster

## Goal

On aarch64 cores with the SHA-512 instructions, SHA-384, SHA-512, and SHA-512/256, with the HMAC and HKDF over them, run pyca/verified-garbage's `vg_sha512_compress_sha512` under rind's own buffering and padding wherever it measures faster than aws-lc's routine, which rind runs there today.

## Plan

Found by the 0.4 report refresh ([kixel-ai/rind#991](https://github.com/kixel-ai/rind/pull/991)) at `3f76a53f`.

- `kixtop` (Apple M4) hashed 16 KB with VG's API in 7.89 µs against rind's 8.89 (1.13×) and 1350 B in 686 against 748 ns, but lost at 64 B (82 against 77 ns). The weekly aarch64 tier's Neoverse N2 ([run 44941104585](https://github.com/kixel-ai/rind/actions/runs/44941104585)) shows the same shape, smaller: VG 12.09 against 12.46 µs at 16 KB, 1062 against 1088 ns at 1350 B, and 126 against 117 ns at 64 B.
- VG's API rows include its own init, buffering, and finalization, so the 64 B loss may be there rather than in its block function. Vendor `vg_sha512_compress_sha512` with `admin/import-vg` and time it under rind's glue against aws-lc's `sha512_block_data_order_hw` on both cores at every hash size the speed bar sets. If it wins or levels at every size, take it everywhere; if it loses only on short input, pick by block count, as aarch64 ChaCha20 picks by length; if it loses at every size under rind's glue, record that in the PR and delete this quest, turning `benchmarks/gaps.toml`'s entry into a reason.
- aws-lc's routine carries rind's own HOL Light proof ([`proofs/`](/proofs/README.md)); VG's carries its Lean proof, which rind imports as an axiom about its wrapper, as [the VG epic](/quest/m2/verified-garbage/README.md) sets out, with `admin/prove vg`'s cosimulation of its instructions, so the ✓ holds either way once both are in place. Update ALGORITHMS.md's aarch64 row and `benchmarks/verified.toml`.
