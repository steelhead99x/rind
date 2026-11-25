# [M] rind is timed on the ESP32-C6 next to every library that builds for it

## Goal

The ESP32-C6 benchmark firmware times rind and, for each operation they share, the RustCrypto and dalek crates that build for `riscv32imac-unknown-none-elf` out of the box, with the same sizes, rounds, and clock, and the results say which other libraries are not buildable on this target and why. The firmware ran once on a board (ESP32-C6 rev v0.2, 19 known answers passed, 7 rounds) and the numbers are in `benchmarks/esp32c6.md`.

## Plan

Drafted 2026-11-20 (Claude), decided with the owner the same day: extra porting work only for rind; any other library that does not build out of the box is listed as not buildable with its exact first error, not patched, forked, or worked around.

- `admin/esp32c6-vendors` builds each library `rind-bench` compares against, alone and with default features off, and records builds or the first error. Its first run found: ring (getrandom has no backend for the target), aws-lc-rs (no C compiler for riscv32), libcrux-ecdh and libcrux-ml-dsa (need `std`) not buildable; the RustCrypto and dalek crates, and libcrux's sha2, sha3, chacha20poly1305, ed25519 and ml-kem, build. A later pass added every other `rind-bench` dev-dependency competitor (libcrux-aes, -ecdsa, -hmac, -hkdf, -rsa, hpke-rs, fips205, blind-rsa-signatures, voprf, spake2plus, vrf-rfc9381, jsonwebtoken, rustls, aws-lc-sys, verified-garbage, graviola, rustls-graviola, openssl, openssl-sys, rustls-openssl); of these libcrux-aes, -hmac, -hkdf, -rsa, fips205, voprf and spake2plus build and the rest are recorded as not buildable.
- `admin/esp32c6/src/vendors.rs` times RustCrypto and dalek for nine operations (SHA-256, SHA-512, SHA3-256, HMAC-SHA256, ChaCha20-Poly1305, AES-128-GCM, Ed25519 sign and verify, X25519) with the operation IDs rind's rows use, and `agree` checks on the host and under qemu that both give the same bytes for what is timed, so a faster row is not a row that did less.
- rind's rows now also cover SHA-1, MD5, AES-256-GCM, PBKDF2-HMAC-SHA256, P-256 ECDH and ECDSA, ML-KEM-768, and ML-DSA-65.
- Still to do, each its own step: rows for XChaCha20-Poly1305, P-384, P-521, RSA, SLH-DSA, Argon2id, HPKE and the libcrux crates; a cycle counter if the C6 exposes one the chip's documentation supports.
- An operation whose heap or stack the board lacks (ML-KEM-768, ML-DSA-65, P-256, checked against the peaks `admin/esp32c6-riscv32 size` measured plus a quarter and 4 KiB) prints `RIND-BENCH v1 <op> lib=rind size_failure=heap|stack need=<n> have=<n>` instead of running, and the ingest records it as a `size-failure` result with no time, so a run completes without a panic. The firmware also builds without its default `bench` feature (`cargo build --release --no-default-features`) as the LED status image: the checks and the LED, no timing rows. Both images were flashed once. The status image's LED showed orange, which does not match the documented blue, green, red; the colour mapping is unverified.
- Open: the RustCrypto SHA-512 row (39.4 ms against rind's 1.30 ms) is most likely the vendor's fully unrolled 52 KB compression function missing the C6's flash instruction cache; rerun on the board with `--cfg sha2_backend_soft="compact"` for a like-for-like number.
- Rows carry `lib=<library>`; `admin/esp32c6-bench-ingest` keeps it. `admin/bench-report` has no C6 host, so these are not rendered into BENCHMARKS.md.

## Required

- [The firmware, sensor example, and ingest script](/quest/m2/bench/esp32-c6-bench.md) - the harness this extends
- [The results document](/quest/m2/bench/esp32-c6-results.md) - where the numbers and the build matrix go
