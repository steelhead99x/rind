# [M] ChaCha20-Poly1305 on 32-bit portable targets beats RustCrypto's on the ESP32-C6

## Goal

On the ESP32-C6 (`riscv32imac`, 160 MHz, code from flash through its instruction cache), rind's ChaCha20-Poly1305 seal of 1350 B takes less time than RustCrypto's `chacha20poly1305` 0.11 in the same firmware, measured on the board against a control built from the same worktree path. 64-bit targets, x86_64, aarch64, and armv7 keep what they run now, and every proof keeps covering what it covered. If the board does not show rind ahead, this quest's PR records the measurement in `benchmarks/esp32c6.md` and deletes the quest.

## Plan

Drafted 2026-11-20 (Claude), owner-requested after the first board run in `benchmarks/esp32c6.md`: rind 778.9 us against RustCrypto's 684.4 us, 1.14x slower. [steelhead99x/rind#274](https://github.com/steelhead99x/rind/pull/274)'s instruction counts put rind 14% above RustCrypto and suspected HACL*'s Poly1305. Measured here per seal (`admin/esp32c6-riscv32 icount` and a per-instruction profile under qemu-riscv32, 1350 B, 22 ChaCha20 blocks and 86 Poly1305 blocks):

| part | rind before | RustCrypto | rind after |
|---|---:|---:|---:|
| ChaCha20 (keystream and XOR) | 51.2k (2,330 a block) | 50.5k | 38.4k (1,670 a block) |
| Poly1305 | 50.7k (590 a block) | 29.3k (340 a block) | 17.7k (206 a block) |
| whole seal | 106,840 | 93,408 | 61,279 |

So the suspicion held for Poly1305, and ChaCha20 was level with RustCrypto's but wasted about 700 instructions a block on a 64-byte keystream array, stored a byte at a time and XORed back a byte at a time.

- Poly1305 on 32-bit portable targets is `low::generic::poly1305_32`: five 26-bit limbs in `u32`s, poly1305-donna-32's radix and carry chain as [steelhead99x/rind#191](https://github.com/steelhead99x/rind/pull/191) has them, without #191's 16-bit-halves layer, which riscv32imac's `mul`/`mulhu` does not need. HACL*'s keeps its limbs in `u64`s, so each product was a full 64-bit multiply (three `mul` and a `mulhu`) and each sum a 64-bit add. Blocks that start on a word load as words. Nothing proves it yet (the proof is planned, see Waiting); tests check it against HACL* and Graviola's 64-bit Poly1305 at every word offset, under ctgrind too. armv7 without NEON keeps HACL*.
- ChaCha20 on 32-bit portable targets keeps HACL*'s proven rounds (`generic::chacha20::rounds`, now `pub(crate)`, body unchanged) and XORs the keystream words into the buffer a word at a time, shifting across two keystream words where the buffer is misaligned (68.2k instructions a seal at offsets 1 and 3, against 61.3k aligned and the control's 107.9k), from one call site so the unrolled rounds stay one 6.3 KB copy. 64-bit targets keep `generic::chacha20::cipher`, which `proofs/` covers on x86_64.
- Not done, with reasons: interleaving two blocks' states (32 words do not fit riscv32's 31 usable registers, so it would spill); Zbb rotates (the C6 has none, so each rotate stays a shift, a shift, and an or, 1,600 of the 1,670 instructions a block); two Poly1305 blocks per reduction with r^2 (saves about 20 of 206 instructions a block, but the column sums pass 2^58 and the carries need 64 bits, so the gain is small and unmeasured).
- Candidate images for an interleaved board run, each from the same worktree path: control, Poly1305 only, ChaCha20 only, both, and both with the double rounds rolled into a loop (1.9 KB of rounds instead of 6.3 KB, 5% more instructions), the last in case the instruction cache decides it. The PR lists their hashes and expected deltas; the numbers that decide this quest come only from the board.

## Waiting

- steelhead99x: flash the candidate images listed in the PR interleaved with the control, and send the logs. Check: the PR body's table holds board medians for every image.
- Maintainer: accepted (option A): 32-bit portable targets run `poly1305_32`, which is **accepted and not yet proven**, ahead of HACL*'s proven Poly1305, on AGENTS.md's rule to run the fastest source and plan its proof. The proof is planned, joining [the portable ChaCha20-Poly1305 proof quest](/quest/m5/verified/chacha20-poly1305-portable.md); none exists yet, and until it does this Poly1305 is covered by differential tests and ctgrind only. HACL*'s was slower at every size on these cores. (B) was keeping HACL*'s Poly1305 and landing only the ChaCha20 change; (C) was waiting for kixel-ai/rind#794, which also adds a 26-bit `generic::poly1305_32` and drops libcrux. The same decision is open in kixel-ai/rind#942's quest.
- Maintainer: the multiply contract. `poly1305_32`, like the HACL* Poly1305 it replaces on these targets, forms each limb product as a 32 by 32 to 64-bit multiply. That is fixed-time on riscv32imac (`mul` and `mulhu`) and on i686, but on a core whose long multiply has operand-dependent latency (Arm's Cortex-M3 `umull` and `umlal`, measured in the compiled `dot` for `thumbv7m-none-eabi`) or no hardware multiply (`riscv32i` calls `__mulsi3`) it is not. Only riscv32imac was measured here. Options: (A) leave it, as HACL* was; (B) narrow the 26-bit path to `target_arch = "riscv32"` with the `m` feature, and keep HACL* elsewhere. Recommendation: B if the maintainers want the timing claim to hold on every 32-bit portable target, once there is a second measured target.

## Related

- [The comparison with RustCrypto and dalek](/quest/m2/bench/esp32-c6-compare.md) - where ChaCha20-Poly1305 lost
- [ChaCha20-Poly1305 is proven on x86_64 without SSE4.1](/quest/m5/verified/chacha20-poly1305-portable.md) - the Aeneas route a proof of `poly1305_32` would take
