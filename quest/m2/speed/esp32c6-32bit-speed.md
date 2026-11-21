# [M] AES-GCM and P-256 signing are faster on 32-bit portable targets

## Goal

On the ESP32-C6 (`riscv32imac`, 160 MHz), rind's AES-GCM and P-256 signing run in fewer cycles than the code they replace, each change measured on the board against a control built from the same worktree path, and what remains slower than RustCrypto is stated.

## Plan

Drafted 2026-11-20 (Claude), owner-requested after the first board run in `benchmarks/esp32c6.md` showed rind losing AES-128-GCM to RustCrypto (2.43 ms against 1.86 ms per 1350 B) and P-256 signing (19.8 ms) slower than its instruction count predicts. Candidates were ranked by `admin/esp32c6-riscv32 icount` (instructions under qemu-riscv32, with `admin/esp32c6/icount-plugin.c`), then timed on the board interleaved against `cand-base`, the control: runs are deterministic, with a spread of about 0%.

- ✅ AES on 32-bit portable targets is RustCrypto's fixsliced `aes` 0.8.4 (`rind/src/low/generic/aes_fixslice32.rs`), taken under Apache-2.0 and named in `LICENSE`, `rind-python/LICENSE`, and `ALGORITHMS.md`. Constant time: a bitsliced circuit, ctgrind-tested. Against the control, AES-128-GCM took 0.878 of its time and AES-256-GCM 0.856.
- ✅ `gcm_mul32_nohw` stays out of line on 32-bit portable targets, since LLVM spilled most of the 96 products when it was inlined three times. AES-128-GCM 0.920, AES-256-GCM 0.932.
- ✅ With both, AES-128-GCM took 0.800 of the control's 2,427 us (about 1,940 us) and AES-256-GCM 0.791 of 2,867 us. RustCrypto's AES-128-GCM is 1,855 us, so rind is still about 5% slower; a separate branch, `claude/q-esp32c6-aes128gcm`, takes AES-128-GCM further, and this quest does not.
- ✅ P-256 on 32-bit portable targets runs s2n-bignum's `p256_scalarmulbase` with block size 4 over a 33 KB table, and verification's width-6 NAF over a 2 KB row of 1G..32G. Sign took 0.841 of the control's time. The same table placed in RAM (a diagnostic image that never lands) took 0.642, which confirms that flash traffic is the cost and leaves headroom a smaller table cannot take. Verify: 0.995, level.
- Other rows moved within about 1%. ChaCha20-Poly1305 is 1.1% slower in two builds, most likely code layout, since nothing in that path changed. ML-DSA-65 sign is too noisy to compare even as a mean of 16 calls.
- ✅ The harness warms each bench twice, since rind builds a key's reusable state on its second use, and times ML-DSA-65 signing 16 calls a round.
- Left alone, with evidence in the PR: x25519 and Ed25519 (same instruction count as dalek), ChaCha20-Poly1305 (imported verified code), and SHA-512 (RustCrypto's 52 KB `compress512` missing the flash cache, not rind's cost).

## Required

- [The ESP32-C6 results](/quest/m2/bench/esp32-c6-results.md) - the board numbers these ratios are against
- [The comparison with RustCrypto and dalek](/quest/m2/bench/esp32-c6-compare.md) - where AES-128-GCM lost
