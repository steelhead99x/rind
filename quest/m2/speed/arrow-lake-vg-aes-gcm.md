# [S] AES-GCM on Intel without AVX-512 runs verified-garbage's code for long messages where it is faster

## Goal

On Intel CPUs with VAES and VPCLMULQDQ but no AVX-512, such as `desktop`'s Arrow Lake, AES-GCM seal and open of long messages run whichever of pyca/verified-garbage's code and BoringSSL's `aes-gcm-avx2-x86_64`, which rind runs today, is faster at each length, measured under rind's glue at every AEAD size the speed bar sets, without slowing short messages or key setup.

## Plan

Found by `desktop`'s first run on two reserved cores ([kixel-ai/rind#1103](https://github.com/kixel-ai/rind/pull/1103); 0.03 other CPUs busy on them), and repeated by a recheck of the same rows (1.112×) and, at 1.08×, by its quiet run the day before.

- At 16 KB, VG's API took 0.90 of rind's time to seal with AES-256 (842 against 934 ns), 0.94 to seal with AES-128 (727 against 776), and 0.92 and 0.94 to open (744 against 807, 859 against 915). ring was level with rind (798 to 958 ns) and aws-lc-rs far behind. rind won at every shorter size: 0.36 to 0.76 of VG's time at 32 B and 0.89 to 0.92 at 1350 B.
- First find which VG routines its API runs on this CPU, which has VAES, VPCLMULQDQ, and AVX-VNNI but neither AVX-512 nor AVX-IFMA. Then time them under rind's glue (`rind/src/low/x86_64/aes_gcm_vaes.rs`) against BoringSSL's AVX2 routines on `desktop`, seal and open, every key size and AEAD size.
- Switch only by length, above the crossover, since rind leads at 32 B and 1350 B, and only if the switch reuses rind's key powers or builds VG's lazily: key setup is on QUIC's hot path, and [kixel-ai/rind#955](https://github.com/kixel-ai/rind/pull/955) found VG's key-power table raised it to 257 to 274 ns. Pick by vendor, as `rind/src/low/x86_64/sha512.rs` does with `is_intel`, so AMD keeps its measured choice. If VG wins nowhere under rind's glue, record the numbers in the PR, turn `benchmarks/gaps.toml`'s `desktop` AES-GCM entry into a reason, and delete this quest.

## Hosts

- linux - `desktop` is the only Intel host without AVX-512
