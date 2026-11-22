# rind on the ESP32-C6

Draft. The ESP32-C6 is a 160 MHz `riscv32imac` core. rind runs its portable backend there: no hardware SHA-512 or AES is used. **Nothing below has been measured on the board.** The first table was measured without it, by `admin/esp32c6-riscv32 size`; the second is `TODO` until the firmware in `admin/esp32c6/firmware` has run on a board.

## Measured without the board

Cross-built for `riscv32imac-unknown-none-elf` at opt-level 3 with LTO, rustc 1.98.1, rind at the commit this file was written on, run under `qemu-riscv32` (user mode). Code is `.text` plus `.rodata` over the harness alone ("7823 B code": the runner, with a no-op check that keeps its per-check loop in the baseline), so an algorithm that shares code with another shows what it adds over the harness, not over the others. Stack is the distance from the checking function's stack pointer to the deepest byte touched in a painted region (re-measured after a fix that had left every figure 256 bytes low) and heap the peak of live allocator bytes, both from one run of that algorithm's known-answer check inside the all-algorithms build, so inlining can move them a little in another build. They are properties of the code, and not time.

| algorithm | code over harness (B) | peak stack (B) | peak heap (B) | known answer |
|---|---|---|---|---|
| sha256 | 12005 | 800 | 32 | ok |
| sha512 | 7329 | 852 | 64 | ok |
| sha3-256 | 7495 | 808 | 32 | ok |
| hmac-sha256 | 14594 | 1040 | 32 | ok |
| hkdf-sha256 | 15784 | 2320 | 52 | ok |
| chacha20poly1305 | 21485 | 2376 | 468 | ok |
| aes128-gcm | 25065 | 2612 | 16 | ok |
| aes256-gcm | 25099 | 2612 | 16 | ok |
| x25519 | 65507 | 3800 | 64 | ok |
| ed25519 | 96690 | 5816 | 64 | ok |
| mlkem768 | 38133 | 41460 | 12288 | ok |
| mldsa65 | 34554 | 40532 | 84992 | ok |
| p256-ecdsa | 174927 | 17484 | 0 | ok |
| sensor | 134659 | 11368 | 206 | ok |

`mlkem768` and `mldsa65` check a round trip, not a vector, and `p256-ecdsa` and `sensor` a round trip and a rejected change; the rest match published vectors. The randomness in that run is a fixed, insecure stream.

## Measured on the board

Board: ESP32-C6 (chip variant and flash size `TODO`: confirm with `espflash board-info`). Firmware commit `TODO`. CPU clock 160 MHz (the firmware sets it; `TODO` confirm in the log). Supply `TODO`. Temperature `TODO`. Rounds `TODO`, iterations per round as printed. Time comes from the chip's system timer, which ticks at 16 MHz, but the firmware reads it in whole microseconds (`Instant::now().duration_since_epoch().as_micros()`), so each timestamp resolves 1 us and not 62.5 ns. A round times `iters` calls between two such timestamps and divides, so a per-call value is a mean over those calls with a granularity of 1 us divided by `iters`; each row is a median over rounds of that per-call time. Operations that take a few microseconds per call are therefore only as precise as their `iters` allows.

| operation | median (us) | min (us) | max (us) | rounds | iters |
|---|---|---|---|---|---|
| sha256 | TODO | TODO | TODO | TODO | TODO |
| sha512 | TODO | TODO | TODO | TODO | TODO |
| sha3-256 | TODO | TODO | TODO | TODO | TODO |
| hmac-sha256 | TODO | TODO | TODO | TODO | TODO |
| hkdf-sha256 | TODO | TODO | TODO | TODO | TODO |
| chacha20poly1305 | TODO | TODO | TODO | TODO | TODO |
| aes128-gcm | TODO | TODO | TODO | TODO | TODO |
| x25519 | TODO | TODO | TODO | TODO | TODO |
| ed25519 sign | TODO | TODO | TODO | TODO | TODO |
| ed25519 verify | TODO | TODO | TODO | TODO | TODO |

No other library was timed: aws-lc-rs and ring do not build for `riscv32imac` here without a C toolchain, so these rows make no claim against them. ML-KEM, ML-DSA, and P-256 are not timed yet.

## How these numbers were made

```
admin/esp32c6-riscv32 size       # first table
admin/esp32c6-riscv32 firmware   # builds the board image
espflash flash --port PORT --chip esp32c6 <elf>
admin/esp32c6-bench-ingest LOG --out esp32c6.json   # second table
```
