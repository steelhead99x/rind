# [M] ChaCha20-Poly1305 on the ESP32-S3 (Xtensa LX7) is faster than RustCrypto's, and the same slowness is found elsewhere

## Goal

On the ESP32-S3 (`xtensa-esp32s3-none-elf`, Xtensa LX7), rind's ChaCha20-Poly1305 seal and open take less time than RustCrypto's `chacha20poly1305` 0.10 at every size from 16 B to 1500 B, measured on the board in one firmware with a harness that gives both libraries the same work (the first run's open rows did not, see Plan). Ed25519 signing and verification stay faster than dalek's. Every other backend keeps what it runs, and the constant-time claims hold: no branch on a secret in what this changes. If the board does not show rind ahead, the quest's PR records the measurement and deletes the quest.

## Plan

Drafted 2026-11-21 (Claude), owner-requested after the first S3 board run. MEASURED on one board (ESP32-S3 v0.2, 1 us timestamps, median of 15 rounds, [halow-lora-workshop](https://github.com/steelhead99x/halow-lora-workshop) `firmware-s3` at 76c633c, rind at e1321f2de, which is before the 26-bit Poly1305 of steelhead99x/rind#275):

| size | seal rind | seal RustCrypto | open rind | open RustCrypto |
|---:|---:|---:|---:|---:|
| 16 B | 203.2 us | 99.2 us | 211.5 us | 68.8 us |
| 51 B | 242.8 | 127.0 | 251.2 | 91.0 |
| 243 B | 477.1 | 355.6 | 488.1 | 174.2 |
| 255 B | 478.0 | 357.2 | 489.1 | 174.1 |
| 1500 B | 2014.2 | 1857.5 | 2040.8 | 718.6 |

Ed25519 sign 45.1 ms rind against 148.7 ms RustCrypto, verify 67.2 against 76.9 ms.

Root cause, from the source and the image's disassembly (no hardware was touched; nothing below is a board measurement unless it says so):

- The firmware never sets a CPU clock: `esp_hal::init(Config::default())` selects `CpuClock::default()`, which is 80 MHz on the S3 (`esp-hal` 1.2.2, `soc/esp32s3/clocks.rs`), not 240 MHz. Every time above is at 80 MHz.
- The open rows are not like for like. The harness decrypts RustCrypto's open in place into the one buffer it reuses, so after the first call the buffer holds plaintext, the tag fails, and `decrypt_in_place_detached` returns before decrypting: the row times the MAC only. rind's open copies the ciphertext into a scratch buffer each call, so it always does MAC, decrypt, and two copies. The RustCrypto open rows are the MAC alone; the 2.8x at 1500 B is that, not a slow rind open. The KAT checks only seal.
- Fitting the rind rows to `a*P + b*C + F` (P a Poly1305 block, C a ChaCha20 block, F fixed per call) gives P = 13.3 us (1,070 cycles, HACL*'s Poly1305, which that rind ran), C = 24.8 us (1,980 cycles) and F = 113 us, which reproduces all five seal rows within 1%. RustCrypto's open rows give its P = 7.0 us, C = 30.5 us and F = 14 us.
- F is 8,000 cycles a call. The harness builds and drops a `Key` per call, and `Drop` for the key's `Inner` wipes the whole enum, sized for AES-GCM, through `portable::cpu::zero_bytes`: one volatile byte store at a time. On Xtensa each volatile access is preceded by `memw`, so the compiled wipe is `movi`, `add.n`, `memw`, `s8i` per byte (seen in the linked image: 1,370 `memw`). The same wipe runs for every keyed value on every portable target.
- ChaCha20 spent 960 of its 2,200 instructions a block on rotates: LLVM's Xtensa backend emits `slli`, `extui`, `or` for each, where `ssai` and `src` is two (one `ssai` serves four rotates of one distance when the four quarter rounds run side by side).
- The 26-bit `generic::poly1305_32` of #275 already runs on Xtensa (32-bit pointers) and compiles to `mull` plus `muluh`; the S3's core has `MUL32` and `MUL32_HIGH` (`xtensa-esp32s3-elf-gcc -dM`). But LLVM's Xtensa backend adds two `u64`s as `add` and a conditional branch on the carry (`bltu`), 54 of them in `Poly1305::blocks`, so the secret limbs' carries decide a branch: a timing dependence the portable backend's rule forbids. The same pattern is in every 64-bit add in the image.

What this quest changes (each its own PR, stacked on #275):

1. `portable::cpu::zero_bytes` is one `memset` and an opaque use of the pointer (`black_box`), not a volatile byte loop. All portable targets.
2. ChaCha20 on Xtensa: `ssai` once and `src` four times per rotate step, in `portable::chacha20`.
3. Poly1305 on Xtensa: each limb product split at bit 28 into a low and a high `u32` sum so no `u64` add exists, and the tag's `+ s` in 16-bit halves. Same limbs and carries as the `u64` version, checked by a test.

Not done here: a proof for any of it; RustCrypto's `poly1305`, which has the same carry branches; the carry branches in SHA-512 (`sha512_rolled`), Ed25519 and P-256 on Xtensa, listed below as follow-ups.

Validation plan: unit tests on the host for each change (RFC 8439, the existing differential tests against HACL* and the 64-bit Poly1305, a new test that the split and wide reductions agree at the edges of their bounds, the `tests/zeroing.rs` suite), clippy and the strict gate, the firmware's in-image RFC 8439 and RFC 8032 known answers on the board, and interleaved board images from one worktree path (control = #275's head; variants listed in the PR).

## Waiting

- steelhead99x: flash the images listed in the PR, interleaved with the control, with `run-board.sh`, and send the logs. Check: the PR body's table holds board medians for every image.
- Maintainer: whether the 26-bit Poly1305 stays on every 32-bit portable target or narrows to riscv32 with the M extension (the open decision in [the C6 ChaCha20 quest](/quest/m2/speed/esp32c6-chacha20poly1305.md)). The S3's `mull` and `muluh` are fixed-time on this core as far as the ISA manual says; only the S3's timing has not been measured for operand dependence.

## Related

- [ChaCha20-Poly1305 on 32-bit portable targets](/quest/m2/speed/esp32c6-chacha20poly1305.md) - the 26-bit Poly1305 this builds on
- [The ESP32-C6 comparison](/quest/m2/bench/esp32-c6-compare.md) - the harness shape the S3 rows follow
