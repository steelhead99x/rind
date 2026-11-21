# [M] rind's AES-GCM beats RustCrypto's on the ESP32-C6

## Goal

On the ESP32-C6 (`riscv32imac`, 160 MHz, code from flash through its instruction cache), rind's AES-128-GCM seals 1350 bytes in less time than RustCrypto's `aes-gcm` (1,855 us on the board), measured by the bench firmware against a control built from the same worktree path, interleaved, and AES-256-GCM is no slower than the control. Every change keeps the portable backend's constant-time rules: no secret-dependent branch, memory index, or variable-time instruction.

## Plan

Drafted 2026-11-20 (Claude), owner-requested after [the 32-bit speed quest](/quest/m2/speed/esp32c6-32bit-speed.md) left rind's AES-128-GCM at about 1,940 us against RustCrypto's 1,855 us. Under qemu-riscv32 rind already ran fewer instructions (276k against 286k) but took more cycles each: a least-squares fit of the board's medians to the qemu instruction mix of 25 compute-bound rows over four images puts `mulhu` at about 1.2 cycles more than `mul` and a load used by the next instruction at about 1 more, and rind's GHASH ran 12k `mulhu` a seal where RustCrypto runs none.

- GHASH on 32-bit portable targets: Karatsuba three levels down to 27 products of 16-bit halves, each nine `mul`s of operands masked to every third bit, so the product fits the low word and no `mulhu` runs; the key's halves are split and masked once at key setup. Rejected: 4- and 8-bit tables (a secret index, which rind forbids, and scanning a table in constant time costs more than the multiply), two blocks a reduction with the key's square (measured no fewer instructions), and the nine 32-bit products unrolled (3x the code for 0.7% fewer instructions).
- AES (RustCrypto's fixsliced `aes`): counter blocks in and keystream out as words, not bytes; AES-128 and AES-256 with every round unrolled; MixColumns blends by one mask, so the S-box spills less; CTR XORs as words where the buffer is word-aligned.
- Each step is a firmware image in `/home/kdouglas/.cache/c6-fw/aes-*.elf`, built from one worktree path, ranked by instructions under `admin/esp32c6-riscv32 icount` and by the fitted cycle model; the board decides which land.
- Left for later: fusing CTR's XOR with GHASH's load of the same words (an estimated 1.5%), and AES-192, which keeps its loop.

## Required

- [The 32-bit speed quest](/quest/m2/speed/esp32c6-32bit-speed.md) - its fixsliced AES and board control this builds on
- [The comparison with RustCrypto and dalek](/quest/m2/bench/esp32-c6-compare.md) - the RustCrypto row this has to beat
