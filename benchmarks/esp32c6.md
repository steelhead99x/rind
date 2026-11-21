# rind on the ESP32-C6

Draft. The ESP32-C6 is a 160 MHz `riscv32imac` core. rind runs its portable backend there: no hardware SHA-512 or AES is used. **Nothing below has been measured on the board.** The first table was measured without it, by `admin/esp32c6-riscv32 size`; the second is `TODO` until the firmware in `admin/esp32c6/firmware` has run on a board.

## Measured without the board

Cross-built for `riscv32imac-unknown-none-elf` at opt-level 3 with LTO, rustc 1.98.1, rind at the commit this file was written on, run under `qemu-riscv32` (user mode). Code is `.text` plus `.rodata` over the harness alone ("7047 B code"), so an algorithm that shares code with another shows what it adds over the harness, not over the others. Stack is the deepest byte touched in a painted region and heap the peak of live allocator bytes, both from one run of that algorithm's known-answer check inside the all-algorithms build, so inlining can move them a little in another build. They are properties of the code, and not time.

| algorithm | code over harness (B) | peak stack (B) | peak heap (B) | known answer |
|---|---|---|---|---|
| sha256 | 12681 | 544 | 32 | ok |
| sha512 | 8013 | 596 | 64 | ok |
| sha3-256 | 8173 | 552 | 32 | ok |
| hmac-sha256 | 15262 | 784 | 32 | ok |
| hkdf-sha256 | 16444 | 2032 | 52 | ok |
| chacha20poly1305 | 22161 | 2120 | 468 | ok |
| aes128-gcm | 25741 | 2356 | 16 | ok |
| aes256-gcm | 25775 | 2356 | 16 | ok |
| x25519 | 66191 | 3544 | 64 | ok |
| ed25519 | 97382 | 5560 | 64 | ok |
| mlkem768 | 38811 | 41204 | 12288 | ok |
| mldsa65 | 35230 | 40276 | 84992 | ok |
| p256-ecdsa | 175571 | 17228 | 0 | ok |
| sensor | 134561 | 11608 | 206 | ok |

`mlkem768` and `mldsa65` check a round trip, not a vector, and `p256-ecdsa` and `sensor` a round trip and a rejected change; the rest match published vectors. The randomness in that run is a fixed, insecure stream.

## Measured on the board

Board: ESP32-C6 (chip variant and flash size `TODO`: confirm with `espflash board-info`). Firmware commit `TODO`. CPU clock 160 MHz (the firmware sets it; `TODO` confirm in the log). Supply `TODO`. Temperature `TODO`. Rounds `TODO`, iterations per round as printed. Time comes from the chip's system timer, which ticks at 16 MHz, so it resolves 62.5 ns; each row is a median over rounds of the per-call time.

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
| x25519 | TODO | TODO | TODO | TODO | TODO |
| (every other operation in the lists below) | TODO | TODO | TODO | TODO | TODO |

No other library was timed: aws-lc-rs and ring do not build for `riscv32imac` here without a C toolchain, so these rows make no claim against them. ML-KEM, ML-DSA, and P-256 are not timed yet.

## Which comparison libraries build for the C6

`admin/esp32c6-vendors` builds each library rind-bench compares rind with, alone, for `riscv32imac-unknown-none-elf` with default features off, patching nothing. "Builds" means the crate compiles for the target, not that it fits or runs. A library that does not build out of the box is listed with its first error, as decided with the owner: rind gets porting work, no other library does. rind itself needs `--cfg getrandom_backend="custom"` on this target, which the harness sets; ring stops at getrandom's unsupported-target error without a backend.

| crate | rind-bench times it for | result | first error |
|---|---|---|---|
| sha2 | SHA-256, SHA-512 | builds |  |
| sha3 | SHA-3 | builds |  |
| sha1 | SHA-1 | builds |  |
| md-5 | MD5 | builds |  |
| hmac | HMAC | builds |  |
| hkdf | HKDF | builds |  |
| pbkdf2 | PBKDF2 | builds |  |
| aes-gcm | AES-GCM | builds |  |
| chacha20poly1305 | ChaCha20-Poly1305, XChaCha20-Poly1305 | builds |  |
| ed25519-dalek | Ed25519 | builds |  |
| x25519-dalek | X25519 | builds |  |
| p256 | P-256 | builds |  |
| p384 | P-384 | builds |  |
| p521 | P-521 | builds |  |
| rsa | RSA | builds |  |
| ml-kem | ML-KEM | builds |  |
| ml-dsa | ML-DSA | builds |  |
| slh-dsa | SLH-DSA | builds |  |
| argon2 | Argon2id | builds |  |
| hpke | HPKE | builds |  |
| libcrux-sha2 | SHA-2 | builds |  |
| libcrux-sha3 | SHA-3 | builds |  |
| libcrux-chacha20poly1305 | ChaCha20-Poly1305 | builds |  |
| libcrux-ed25519 | Ed25519 | builds |  |
| libcrux-ecdh | X25519, P-256 ECDH | not buildable on this target | error[E0463]: can't find crate for `std` / error: could not compile `rand` (lib) due to 1 previous error |
| libcrux-ml-kem | ML-KEM | builds |  |
| libcrux-ml-dsa | ML-DSA | not buildable on this target | error[E0463]: can't find crate for `std` / error: could not compile `libcrux-ml-dsa` (lib) due to 1 previous error |
| ring | everything ring has | not buildable on this target | error: target is not supported, for more information see: https://docs.rs/getrandom/#unsupported-targets / error: could not compile `getrandom` (lib) due to 1 previous error |
| aws-lc-rs | everything aws-lc-rs has | not buildable on this target | warning: aws-lc-sys@0.47.0: Compiler family detection failed due to error: ToolNotFound: failed to find tool "riscv32-unknown-elf-gcc": No such file or directory (os error 2) / warning: aws-lc-sys@0.47.0: Compiler family detection failed due to error: ToolNotFound: failed to find tool "riscv32-unkno |

The `hpke` row is from a second run with its `aes` and `hkdfsha2` features: the first, with neither, stops at the crate's own "At least one AEAD feature must be enabled".

## What the firmware times

On the board it times rind for sha256, sha512, sha3-256, sha1, md5, hmac-sha256, hkdf-sha256, pbkdf2-hmac-sha256 (1000 iterations), chacha20poly1305, aes128-gcm, aes256-gcm, x25519, ed25519, P-256 ECDH and ECDSA, ML-KEM-768, and ML-DSA-65, and RustCrypto and dalek for the nine operations both have (SHA-256, SHA-512, SHA3-256, HMAC-SHA256, ChaCha20-Poly1305, AES-128-GCM, Ed25519 sign and verify, X25519). `vendors-agree` checks, on the host and on riscv32imac under qemu, that rind and each of those give the same bytes, so a row is not faster because it did less. Not timed yet, though rind has them: XChaCha20-Poly1305, P-384, P-521, RSA, SLH-DSA, Argon2id, HPKE, and the libcrux crates' rows (libcrux builds for sha2, sha3, chacha20poly1305, ed25519, and ml-kem, but no row calls them yet). Each is `TODO` for a reason a person can act on: porting its row, or sizing the heap first (RSA, SLH-DSA, and Argon2id may not fit 140 KB of heap; the firmware records a heap failure as a panic, which the ingest script refuses, so a size failure must be added as its own row before that run).

## How these numbers were made

```
admin/esp32c6-riscv32 size       # first table
admin/esp32c6-riscv32 firmware   # builds the board image
espflash flash --port PORT --chip esp32c6 <elf>
admin/esp32c6-bench-ingest LOG --out esp32c6.json   # second table
```
