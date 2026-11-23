# rind on the ESP32-C6

The ESP32-C6 is a 160 MHz `riscv32imac` core. rind runs its portable backend there: no hardware SHA-512 or AES is used. The first table was measured without a board, by `admin/esp32c6-riscv32 size`. The rest was measured on a real board, one run of the firmware in `admin/esp32c6/firmware`, with 19 known-answer checks passed and `failed=0`.

## Measured without the board

Cross-built for `riscv32imac-unknown-none-elf` at opt-level 3 with LTO, rustc 1.98.1, rind at the commit this file was written on, run under `qemu-riscv32` (user mode). Code is `.text` plus `.rodata` over the harness alone ("7823 B code": the runner, with a no-op check that keeps its per-check loop in the baseline), so an algorithm that shares code with another shows what it adds over the harness, not over the others. Stack is the distance from the checking function's stack pointer to the deepest byte touched in a painted region (re-measured after a fix that had left every figure 256 bytes low; it is a high-water estimate of bytes written, floored at the 256-byte unpainted guard, so stack reserved but never written does not show) and heap the peak of live allocator bytes, both from one run of that algorithm's known-answer check inside the all-algorithms build, so inlining can move them a little in another build. They are properties of the code, and not time.

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

Board: one ESP32-C6, chip revision v0.2, 4 MB flash, CPU clock 160 MHz (the firmware sets it and prints `cpu_mhz=160`). The benchmark image is 785,808 B, 19.0% of the 4,128,768 B app partition (ELF text 1,092,038 B, data 1,744 B, bss 144,060 B including the 140 KB heap). Firmware built from branch `claude/q-esp32c6-compare`, rustc 1.98.1, opt-level 3, LTO, `panic = "abort"`; ELF sha256 `4eb27928...`. Rounds: 7. Iterations per round are in the tables (8 for 1350 B operations, 16 for HKDF, 2 for X25519 and Ed25519, 1 for the slow ones). Time comes from the chip's system timer, which ticks at 16 MHz, but the firmware reads it in whole microseconds (`Instant::now().duration_since_epoch().as_micros()`), so each timestamp resolves 1 us and not 62.5 ns. A round times `iters` calls between two such timestamps and divides, so a per-call value is a mean over those calls with a granularity of 1 us divided by `iters`; each row is the median over rounds of that per-call time, with the min and max over rounds. An operation that takes a few microseconds per call is only as precise as its `iters` allows. Supply and temperature were not recorded (`TODO`, not measurable from the log). The board's MAC and serial port are not recorded here; `admin/esp32c6-bench-ingest` drops them.

**Workload note.** The board rows below come from a firmware image built before the benchmark workloads were aligned with `rind-bench`: the HMAC-SHA256, ChaCha20-Poly1305, AES-GCM, X25519 and Ed25519 rows (rind and vendors alike) were measured on the previous workload (HMAC with the key built outside the timed call, empty associated data in the AEAD rows, X25519 under the old ID `x25519/{lib}` and, for dalek, against the basepoint, and the earlier Ed25519 messages). The source now times the canonical workloads (HMAC keyed per message, 32 B associated data, `x25519-ecdh-stored/{lib}` against the same peer key for both libraries, rind-bench's Ed25519 messages), so those rows need a re-run on the board before they are compared with other platforms. The SHA, HKDF, PBKDF2, P-256, ML-KEM and ML-DSA rows are unaffected.

The raw log held 12 copies of the summary (the firmware repeats it); they agree, and the first was ingested. The 19 checks are sha256, sha512, sha3-256, hmac-sha256, hkdf-sha256, chacha20poly1305, aes128-gcm, aes256-gcm, x25519, ed25519, mlkem768, mldsa65, p256-ecdsa, sha1, md5, pbkdf2-sha256, p256-ecdh, vendors-agree, and sensor.

LED status firmware: flashed; the owner observed an orange LED, which does not match the documented blue (running), green (passed), red (failed). The colour mapping (possibly WS2812 GRB/RGB order or brightness mixing) is unverified. The serial-side result above is the evidence that the checks passed, not the LED.

### rind

| operation | median (us) | min (us) | max (us) | rounds | iters |
|---|---|---|---|---|---|
| sha256 | 653.4 | 653.4 | 662.2 | 7 | 8 |
| sha512 | 1,299.6 | 1,299.5 | 1,308.5 | 7 | 8 |
| sha3-256 | 1,262.2 | 1,262.1 | 1,269.2 | 7 | 8 |
| sha1 | 389.6 | 389.6 | 394.1 | 7 | 8 |
| md5 | 146.6 | 146.5 | 152.5 | 7 | 8 |
| hmac-sha256 | 688.2 | 688.1 | 693.5 | 7 | 8 |
| hkdf-sha256 extract+expand | 287.5 | 287.5 | 292.0 | 7 | 16 |
| pbkdf2-hmac-sha256, 1000 iterations | 70,283.0 | 70,283.0 | 70,300.0 | 7 | 1 |
| chacha20poly1305 | 778.9 | 778.9 | 789.2 | 7 | 8 |
| aes128-gcm | 2,426.8 | 2,426.8 | 2,436.4 | 7 | 8 |
| aes256-gcm | 2,866.6 | 2,866.6 | 2,878.0 | 7 | 8 |
| x25519 | 23,330.5 | 23,330.0 | 23,388.0 | 7 | 2 |
| ed25519 sign | 16,257.0 | 16,253.0 | 16,264.0 | 7 | 2 |
| ed25519 verify | 24,351.5 | 24,351.5 | 24,378.5 | 7 | 2 |
| p256 ECDH | 26,738.0 | 26,714.0 | 26,870.0 | 7 | 1 |
| p256 ECDSA sign | 19,839.0 | 19,826.0 | 19,855.0 | 7 | 1 |
| p256 ECDSA verify | 29,051.0 | 28,954.0 | 32,182.0 | 7 | 1 |
| ML-KEM-768 encaps | 2,555.0 | 2,554.0 | 2,585.0 | 7 | 1 |
| ML-KEM-768 decaps | 4,390.0 | 4,376.0 | 4,460.0 | 7 | 1 |
| ML-DSA-65 sign (high variance) | 65,706.0 | 14,536.0 | 167,501.0 | 7 | 1 |
| ML-DSA-65 verify | 5,374.0 | 5,373.0 | 26,574.0 | 7 | 1 |

**ML-DSA-65 sign has high variance:** the seven rounds ran from 14.5 ms to 167.5 ms (median 65.7 ms), because the signing loop rejects and retries a random number of times and each round signs once. Read its median as one of seven draws, not a stable figure. ML-DSA-65 verify's max (26.6 ms) is also well above its median (5.4 ms), from a single round. ML-KEM-768 (2.6 ms encaps, 4.4 ms decaps) and ML-DSA-65 are faster than the P-256 and Ed25519 rows, which is plausible for lattice schemes but is not cross-checked on another implementation here; their known-answer checks are round trips, not vectors.

### rind against the vendors that build

RustCrypto (`sha2`, `sha3`, `hmac`, `chacha20poly1305`, `aes-gcm`) and dalek (`ed25519-dalek`, `x25519-dalek`), same board, same firmware, same opt-level, same timer, default features off. `vendors-agree` confirms rind and each vendor produce the same bytes for these operations.

| operation (1350 B where a size applies) | rind (us) | vendor | vendor (us) | rind vs vendor |
|---|---|---|---|---|
| sha256 | 653.4 | RustCrypto | 686.0 | rind 1.05x faster |
| sha512 | 1,299.6 | RustCrypto | 39,409.6 | rind 30.32x faster |
| sha3-256 | 1,262.2 | RustCrypto | 2,458.4 | rind 1.95x faster |
| hmac-sha256 | 688.2 | RustCrypto | 667.8 | rind 1.03x slower |
| chacha20poly1305 | 778.9 | RustCrypto | 684.4 | rind 1.14x slower |
| aes128-gcm | 2,426.8 | RustCrypto | 1,855.1 | rind 1.31x slower |
| x25519 | 23,330.5 | dalek | 23,325.0 | rind 1.00x slower |
| ed25519 sign | 16,257.0 | dalek | 31,150.5 | rind 1.92x faster |
| ed25519 verify | 24,351.5 | dalek | 31,749.0 | rind 1.30x faster |

Where rind loses: AES-128-GCM (2,426.8 us against RustCrypto's 1,855.1 us, 1.31x slower), ChaCha20-Poly1305 (778.9 us against 684.4 us, 1.14x slower), and HMAC-SHA256 (688.2 us against 667.8 us, 1.03x slower, close to noise). rind is 1.05x faster on SHA-256, 1.9x on SHA3-256, 1.9x on Ed25519 sign and 1.3x on verify, and level on X25519 (23.33 ms against 23.33 ms). The 30x SHA-512 gap needs the next section before it is read as a result.

### The SHA-512 gap is a flash-cache effect, not the algorithm

RustCrypto's SHA-512 took 39.4 ms for 1350 B against rind's 1.30 ms (30x), while its SHA-256 is within 5% of rind's. That is about 570,000 cycles per 128 B block, 7,000 per round, which no instruction count explains. Checked, not guessed: the row is built the same way as rind's (same crate profile, opt-level 3, LTO, `codegen-units = 1`, no `asm` feature; `sha2` 0.11 has no riscv32 assembly or `Zknh` path, so it uses its portable `soft` backend, whose default is fully unrolled). In the benchmark ELF that unrolled `sha2::sha512::compress512` is 52,484 B of code, against 14,718 B for `compress256`. The C6 runs code from flash through a 32 KB instruction cache (Espressif's documented figure; not measured here), so a loop body that does not fit refetches from SPI flash every pass. That is consistent with the size of the gap, and with SHA-256 and the other RustCrypto rows being normal. It is the hypothesis that fits the data; no cache counter was read to confirm it.

Is it fair? It is the vendor crate's default configuration on this target, so it is what a user who adds `sha2` gets, and rind's smaller code is a real advantage there. But it is a property of one build option, not of the SHA-512 algorithm, and it should not be quoted as "rind is 30x faster at SHA-512". `sha2` has a documented `--cfg sha2_backend_soft="compact"` for small targets. The row was kept as measured. **A rerun on hardware is needed** with that cfg (set in RUSTFLAGS for the firmware build, and the row labelled as the compact backend) to get a like-for-like number; until then treat the SHA-512 vendor row as the unrolled-default result only.

### Not timed

XChaCha20-Poly1305, P-384, P-521, RSA, SLH-DSA, Argon2id, HPKE: `TODO`, not run in this firmware (RSA, SLH-DSA and Argon2id may not fit the 140 KB heap). The libcrux crates that build (`libcrux-sha2`, `libcrux-sha3`, `libcrux-chacha20poly1305`, `libcrux-ed25519`, `libcrux-ml-kem`, `libcrux-aes`, `libcrux-hmac`, `libcrux-hkdf`, `libcrux-rsa`, and, with default features off, `libcrux-ecdh`, `libcrux-ecdsa` and `libcrux-ml-dsa`) have no row yet. Temperature: `TODO`.

### Vendors that could not be timed

Not buildable for `riscv32imac-unknown-none-elf` here (details in the next section): `ring` (getrandom has no backend for the target), `aws-lc-rs` (needs a `riscv32-unknown-elf-gcc` C toolchain), and, for the same or similar reasons, `hpke-rs`, `blind-rsa-signatures`, `vrf-rfc9381`, `jsonwebtoken`, `rustls`, `aws-lc-sys`, `verified-garbage`, `graviola`, `rustls-graviola`, `openssl`, `openssl-sys` and `rustls-openssl` (the table below has each one's error). The rest of rind-bench's comparison libraries build: the libcrux crates `libcrux-aes`, `libcrux-hmac`, `libcrux-hkdf`, `libcrux-rsa`, `libcrux-ecdh`, `libcrux-ecdsa` and `libcrux-ml-dsa` as well (each libcrux crate is probed with its default features off: `libcrux-ecdh`, `libcrux-ecdsa` and `libcrux-ml-dsa` were first recorded as needing `std` only because their defaults enable it), and `fips205`, `voprf` and `spake2plus`. No claim is made against the ones that do not build.

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
| libcrux-ecdh | X25519, P-256 ECDH | builds |  |
| libcrux-ml-kem | ML-KEM | builds |  |
| libcrux-ml-dsa | ML-DSA | builds |  |
| libcrux-aes | AES-GCM, AES-CBC/CTR ciphers | builds |  |
| libcrux-ecdsa | P-256 ECDSA | builds |  |
| libcrux-hmac | HMAC | builds |  |
| libcrux-hkdf | HKDF | builds |  |
| libcrux-rsa | RSA | builds |  |
| hpke-rs | HPKE (libcrux backend) | not buildable on this target | error: target is not supported. You may need to define a custom backend see: https://docs.rs/getrandom/0.4.3/#custom-backend / error: could not compile `getrandom` (lib) due to 1 previous error |
| fips205 | SLH-DSA | builds |  |
| blind-rsa-signatures | blind RSA | not buildable on this target | error[E0463]: can't find crate for `std` / error: cannot resolve a prelude import / error: cannot find macro `vec` in this scope |
| voprf | OPRF | builds |  |
| spake2plus | SPAKE2+ | builds |  |
| vrf-rfc9381 | VRF | not buildable on this target | error[E0463]: can't find crate for `std` / error: could not compile `subtle` (lib) due to 1 previous error / error: target is not supported. You may need to define a custom backend see: https://docs.rs/getrandom/0.4.3/#custom-backend |
| jsonwebtoken | JWT | not buildable on this target | error[E0463]: can't find crate for `std` / error[E0463]: can't find crate for `std` / error: cannot resolve a prelude import |
| rustls | TLS handshake and records | not buildable on this target | error: target is not supported, for more information see: https://docs.rs/getrandom/#unsupported-targets / error: could not compile `getrandom` (lib) due to 1 previous error |
| aws-lc-sys | XChaCha20-Poly1305 | not buildable on this target | needs a `riscv32-unknown-elf-gcc` C toolchain (ToolNotFound), as aws-lc-rs |
| verified-garbage | everything verified-garbage has | not buildable on this target | error[E0463]: can't find crate for `std` / error: could not compile `verified-garbage-cpu` (lib) due to 1 previous error |
| graviola | everything graviola has (x86_64 and aarch64 only) | not buildable on this target | error: target is not supported. You may need to define a custom backend see: https://docs.rs/getrandom/0.4.3/#custom-backend / error: could not compile `getrandom` (lib) due to 1 previous error |
| rustls-graviola | TLS (x86_64 and aarch64 only) | not buildable on this target | error[E0463]: can't find crate for `std` / error: cannot resolve a prelude import / error: target is not supported. You may need to define a custom backend see: https://docs.rs/getrandom/0.4.3/#custom-backend |
| openssl | everything OpenSSL has (needs the system library) | not buildable on this target | error: failed to run custom build command for `openssl-sys v0.9.118` |
| openssl-sys | OpenSSL bindings (needs the system library) | not buildable on this target | error: failed to run custom build command for `openssl-sys v0.9.118` |
| rustls-openssl | TLS over OpenSSL | not buildable on this target | error: failed to run custom build command for `openssl-sys v0.9.118` / error[E0463]: can't find crate for `std` |
| ring | everything ring has | not buildable on this target | error: target is not supported, for more information see: https://docs.rs/getrandom/#unsupported-targets / error: could not compile `getrandom` (lib) due to 1 previous error |
| aws-lc-rs | everything aws-lc-rs has | not buildable on this target | warning: aws-lc-sys@0.47.0: Compiler family detection failed due to error: ToolNotFound: failed to find tool "riscv32-unknown-elf-gcc": No such file or directory (os error 2) / warning: aws-lc-sys@0.47.0: Compiler family detection failed due to error: ToolNotFound: failed to find tool "riscv32-unkno |

The `hpke` row is from a second run with its `aes` and `hkdfsha2` features: the first, with neither, stops at the crate's own "At least one AEAD feature must be enabled".

## What the firmware times

On the board it times rind for sha256, sha512, sha3-256, sha1, md5, hmac-sha256, hkdf-sha256, pbkdf2-hmac-sha256 (1000 iterations), chacha20poly1305, aes128-gcm, aes256-gcm, x25519, ed25519, P-256 ECDH and ECDSA, ML-KEM-768, and ML-DSA-65, and RustCrypto and dalek for the nine operations both have. Every one of those rows has a measured number above. Not timed yet, though rind has them: XChaCha20-Poly1305, P-384, P-521, RSA, SLH-DSA, Argon2id, HPKE, and the libcrux rows. Those stay `TODO`; the firmware records a heap or stack shortfall as a `size_failure` row, which the ingest keeps as a result.

## How these numbers were made

```
admin/esp32c6-riscv32 size       # first table
admin/esp32c6-riscv32 firmware   # builds the board image
espflash flash --port PORT --chip esp32c6 <elf>
admin/esp32c6-bench-ingest LOG --out esp32c6.json   # board tables
```
