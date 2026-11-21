# [M] rind is timed on the ESP32-C6 next to every library that builds for it

## Goal

The ESP32-C6 benchmark firmware times rind and, for each operation they share, the RustCrypto and dalek crates that build for `riscv32imac-unknown-none-elf` out of the box, with the same sizes, rounds, and clock, and the results say which other libraries are not buildable on this target and why. Nothing here has run on the board.

## Plan

Drafted 2026-11-20 (Claude), decided with the owner the same day: extra porting work only for rind; any other library that does not build out of the box is listed as not buildable with its exact first error, not patched, forked, or worked around.

- `admin/esp32c6-vendors` builds each library `rind-bench` compares against, alone and with default features off, and records builds or the first error. Its first run found: ring (getrandom has no backend for the target), aws-lc-rs (no C compiler for riscv32), libcrux-ecdh and libcrux-ml-dsa (need `std`) not buildable; the RustCrypto and dalek crates, and libcrux's sha2, sha3, chacha20poly1305, ed25519 and ml-kem, build.
- `admin/esp32c6/src/vendors.rs` times RustCrypto and dalek for nine operations (SHA-256, SHA-512, SHA3-256, HMAC-SHA256, ChaCha20-Poly1305, AES-128-GCM, Ed25519 sign and verify, X25519) with the operation IDs rind's rows use, and `agree` checks on the host and under qemu that both give the same bytes for what is timed, so a faster row is not a row that did less.
- rind's rows now also cover SHA-1, MD5, AES-256-GCM, PBKDF2-HMAC-SHA256, P-256 ECDH and ECDSA, ML-KEM-768, and ML-DSA-65.
- Still to do, each its own step: rows for XChaCha20-Poly1305, P-384, P-521, RSA, SLH-DSA, Argon2id, HPKE and the libcrux crates; a cycle counter if the C6 exposes one the chip's documentation supports.
- An operation whose heap or stack the board lacks (ML-KEM-768, ML-DSA-65, P-256, checked against the peaks `admin/esp32c6-riscv32 size` measured plus a quarter and 4 KiB) prints `RIND-BENCH v1 <op> lib=rind size_failure=heap|stack need=<n> have=<n>` instead of running, and the ingest records it as a `size-failure` result with no time, so a run completes without a panic. The firmware also builds without its default `bench` feature (`cargo build --release --no-default-features`) as the LED status image: the checks and the LED, no timing rows. Neither image was flashed.
- Rows carry `lib=<library>`; `admin/esp32c6-bench-ingest` keeps it. `admin/bench-report` has no C6 host, so these are not rendered into BENCHMARKS.md.

## Required

- [The firmware, sensor example, and ingest script](/quest/m2/bench/esp32-c6-bench.md) - the harness this extends
- [The results document](/quest/m2/bench/esp32-c6-results.md) - where the numbers and the build matrix go
