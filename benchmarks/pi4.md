# Raspberry Pi 4 (Cortex-A72, no crypto extension) against ring and aws-lc-rs

PR numbers below are written `steelhead99x/rind#N` (the fork). They name: #82, the narrow-multiplier schedules (merged as `847a3e3c`); #163, NEON and SSSE3 Argon2 fills on by default (head `fc4d7df0`); #128 and #188, retiring aarch64's proven double scalar multiplication; #187, AES-192-GCM on aws-lc's four-way kernel; #141, P-256 aarch64 keygen; #193, the armv7 ChaCha20 keystream schedule.

`admin/bench-report` times only the hosts in its `HOSTS` table (`nixos`, `desktop`, `nixos2`, `kixtop`, `ovh-iad`, `ovh-sea`), so a Raspberry Pi 4 cannot appear in `BENCHMARKS.md` without changing that settled list. This note records one Pi 4 B run as indicative numbers outside the report, in the style of `benchmarks/armv7-sha256.md`. Nothing in `benchmarks/data` or `BENCHMARKS.md` uses it. Its job is to say what rind does on a core with no AES, PMULL, SHA, or SHA-3 instructions (see `quest/m5/verified/aarch64-no-crypto.md` and [PLATFORMS.md](../PLATFORMS.md)).

## Method

- Host: Raspberry Pi 4 Model B Rev 1.5, 4 x Cortex-A72 (MIDR part `0xd08`, no `aes`, `pmull`, `sha2`, `sha3`), 3.8 GiB, Debian 13, kernel 6.18, aarch64. Governor `ondemand`, maximum 1.8 GHz. Every round started after a 10 s busy-loop warm-up on the timing core, with the frequency at 1.8 GHz and `vcgencmd get_throttled` at `0x0` (no current under-voltage, frequency-cap, or throttle bit) at every round boundary except the end of baseline round 5. The board lost power once before the run; no under-voltage bit appeared during it. `0x80000` ("soft temperature limit has occurred", sticky since boot) was set at the end of baseline round 5 and stayed set, with the core at 65 to 73 degrees C in the baseline and 60 to 66 degrees C in the A/B. It is not a current throttle, and the A/B rounds still read 1.8 GHz.
- Binaries: `rind-bench` cross-built for `aarch64-unknown-linux-gnu` from upstream `main` at `6efcb465` (with `openssl` removed from the bench crate's dev-dependencies, which does not build for the cross target) for the baseline; `steelhead99x/rind#82` head `51fd07cf` built with `--cfg rind_cpu_disable` for the narrow-or-wide A/B; `steelhead99x/rind#163` head `fc4d7df0` against `main` for Argon2.
- One pinned core (core 3) for timing, criterion `--warm-up-time 1 --measurement-time 2`, 5 rounds, each cell the median of the 5 central estimates. ring, aws-lc-rs, and rind run in the same binary. Another job ran single-threaded benchmarks on core 0 for most of the baseline (load average about 2), so the L2 was shared. Rounds that disagree with the median by more than 2 percent are counted in the last column and kept in the median: baseline round 1 ran the first SHA-2 benchmarks at about half speed (a 2x outlier, the first minutes after boot), and round 5 doubled X25519, ChaCha20-Poly1305 open, and nearby rows. The median of 5 ignores one such round per row.
- The A/B interleaves default, `RIND_CPU_DISABLE_wide_mul=1` (narrow), and `RIND_CPU_FORCE_wide_mul=1` (wide), rotating the order each round, with aws-lc-rs timed in the same process as the control. Every aws-lc-rs cell agrees within 1.02 across the three variants.

## Baseline against ring and aws-lc-rs

Values are the median of 5 rounds. Row labels are Criterion's: plain sizes (`32B`, `1200B`, `16KB`) seal under a 32 B AAD (two GHASH blocks), and `quic-32B` to `quic-512B` seal under QUIC's 13 B short-header AAD (one GHASH block), which is why `quic-32B` is about 80 to 90 ns faster than `32B` for the same body. Ratios below 1 mean rind is faster.

| Operation | ring | aws-lc-rs | rind | rind / aws-lc-rs | rind / ring | Rounds within 2% of median (rind) |
|---|---:|---:|---:|---:|---:|---|
| sha256 64B | 0.94 µs | 1.08 µs | 0.88 µs | 0.82x | 0.93x | 4 of 5 |
| sha256 1200B | 7.85 µs | 7.98 µs | 7.79 µs | 0.98x | 0.99x | 4 of 5 |
| sha256 16KB | 104.33 µs | 104.55 µs | 104.23 µs | 1.00x | 1.00x | 4 of 5 |
| sha512 64B | 0.65 µs | 0.81 µs | 0.60 µs | 0.75x | 0.92x | 4 of 5 |
| sha512 1200B | 5.30 µs | 5.46 µs | 5.25 µs | 0.96x | 0.99x | 4 of 5 |
| sha512 16KB | 66.39 µs | 66.70 µs | 66.49 µs | 1.00x | 1.00x | 4 of 5 |
| hmac-sha256 64B | 2.40 µs | 3.41 µs | 2.21 µs | 0.65x | 0.92x | 4 of 5 |
| hmac-sha256 1200B | 9.30 µs | 10.33 µs | 9.12 µs | 0.88x | 0.98x | 4 of 5 |
| hmac-sha256 16KB | 106.08 µs | 107.15 µs | 105.84 µs | 0.99x | 1.00x | 4 of 5 |
| aes128-gcm 32B | 1.26 µs | 1.31 µs | 1.25 µs | 0.95x | 0.99x | 4 of 5 |
| aes128-gcm 1200B | 21.25 µs | 21.32 µs | 21.55 µs | 1.01x | 1.01x | 4 of 5 |
| aes128-gcm 16KB | 279.13 µs | 279.29 µs | 284.24 µs | 1.02x | 1.02x | 4 of 5 |
| aes128-gcm quic-128B | 2.79 µs | 2.87 µs | 2.83 µs | 0.98x | 1.01x | 4 of 5 |
| aes128-gcm quic-256B | 4.96 µs | 5.05 µs | 5.04 µs | 1.00x | 1.02x | 4 of 5 |
| aes128-gcm quic-512B | 9.36 µs | 9.41 µs | 9.46 µs | 1.01x | 1.01x | 4 of 5 |
| aes128-gcm quic-32B | 1.15 µs | 1.24 µs | 1.17 µs | 0.94x | 1.01x | 4 of 5 |
| aes128-gcm quic-64B | 1.71 µs | 1.79 µs | 1.72 µs | 0.96x | 1.00x | 4 of 5 |
| aes256-gcm 32B | 1.53 µs | 1.58 µs | 1.52 µs | 0.96x | 0.99x | 4 of 5 |
| aes256-gcm 1200B | 26.85 µs | 26.93 µs | 27.20 µs | 1.01x | 1.01x | 4 of 5 |
| aes256-gcm 16KB | 353.49 µs | 355.33 µs | 359.27 µs | 1.01x | 1.02x | 4 of 5 |
| aes256-gcm quic-128B | 3.50 µs | 3.58 µs | 3.53 µs | 0.99x | 1.01x | 4 of 5 |
| aes256-gcm quic-256B | 6.27 µs | 6.33 µs | 6.33 µs | 1.00x | 1.01x | 4 of 5 |
| aes256-gcm quic-512B | 11.79 µs | 11.86 µs | 11.94 µs | 1.01x | 1.01x | 4 of 5 |
| aes256-gcm quic-32B | 1.43 µs | 1.51 µs | 1.43 µs | 0.95x | 1.00x | 4 of 5 |
| aes256-gcm quic-64B | 2.12 µs | 2.19 µs | 2.12 µs | 0.97x | 1.00x | 4 of 5 |
| aes128-gcm-open 32B | 1.29 µs | 1.34 µs | 1.25 µs | 0.94x | 0.97x | 4 of 5 |
| aes128-gcm-open 1200B | 21.36 µs | 21.50 µs | 21.73 µs | 1.01x | 1.02x | 4 of 5 |
| aes128-gcm-open 16KB | 280.86 µs | 281.06 µs | 286.59 µs | 1.02x | 1.02x | 4 of 5 |
| aes128-gcm-open quic-128B | 2.84 µs | 2.91 µs | 2.83 µs | 0.97x | 1.00x | 4 of 5 |
| aes128-gcm-open quic-256B | 5.03 µs | 5.09 µs | 5.08 µs | 1.00x | 1.01x | 4 of 5 |
| aes128-gcm-open quic-512B | 9.40 µs | 9.46 µs | 9.53 µs | 1.01x | 1.01x | 4 of 5 |
| aes128-gcm-open quic-32B | 1.19 µs | 1.25 µs | 1.18 µs | 0.94x | 0.99x | 4 of 5 |
| aes128-gcm-open quic-64B | 1.72 µs | 1.80 µs | 1.73 µs | 0.96x | 1.00x | 4 of 5 |
| aes256-gcm-open 32B | 1.55 µs | 1.60 µs | 1.52 µs | 0.95x | 0.98x | 4 of 5 |
| aes256-gcm-open 1200B | 26.98 µs | 27.03 µs | 27.37 µs | 1.01x | 1.01x | 4 of 5 |
| aes256-gcm-open 16KB | 355.04 µs | 355.18 µs | 359.34 µs | 1.01x | 1.01x | 4 of 5 |
| aes256-gcm-open quic-128B | 3.54 µs | 3.60 µs | 3.55 µs | 0.98x | 1.00x | 4 of 5 |
| aes256-gcm-open quic-256B | 6.31 µs | 6.37 µs | 6.37 µs | 1.00x | 1.01x | 4 of 5 |
| aes256-gcm-open quic-512B | 11.84 µs | 11.95 µs | 11.94 µs | 1.00x | 1.01x | 4 of 5 |
| aes256-gcm-open quic-32B | 1.45 µs | 1.54 µs | 1.45 µs | 0.94x | 1.00x | 4 of 5 |
| aes256-gcm-open quic-64B | 2.14 µs | 2.21 µs | 2.14 µs | 0.97x | 1.00x | 3 of 5 |
| chacha20poly1305 32B | 0.83 µs | 0.87 µs | 0.81 µs | 0.93x | 0.98x | 4 of 5 |
| chacha20poly1305 1200B | 5.09 µs | 5.14 µs | 5.06 µs | 0.98x | 0.99x | 4 of 5 |
| chacha20poly1305 16KB | 64.08 µs | 64.22 µs | 64.06 µs | 1.00x | 1.00x | 4 of 5 |
| chacha20poly1305 quic-128B | 0.99 µs | 1.04 µs | 0.98 µs | 0.94x | 0.99x | 4 of 5 |
| chacha20poly1305 quic-256B | 1.39 µs | 1.46 µs | 1.38 µs | 0.94x | 0.99x | 4 of 5 |
| chacha20poly1305 quic-512B | 2.56 µs | 2.61 µs | 2.53 µs | 0.97x | 0.99x | 3 of 5 |
| chacha20poly1305-open 32B | 0.86 µs | 0.86 µs | 0.82 µs | 0.96x | 0.96x | 3 of 5 |
| chacha20poly1305-open 1200B | 5.68 µs | 5.67 µs | 5.64 µs | 1.00x | 0.99x | 3 of 5 |
| chacha20poly1305-open 16KB | 66.19 µs | 66.25 µs | 66.18 µs | 1.00x | 1.00x | 4 of 5 |
| chacha20poly1305-open quic-128B | 1.04 µs | 1.03 µs | 0.99 µs | 0.96x | 0.96x | 4 of 5 |
| chacha20poly1305-open quic-256B | 1.93 µs | 1.93 µs | 1.90 µs | 0.99x | 0.98x | 4 of 5 |
| chacha20poly1305-open quic-512B | 3.10 µs | 3.12 µs | 3.07 µs | 0.98x | 0.99x | 4 of 5 |
| x25519-ecdh | 299.18 µs | 114.88 µs | 218.15 µs | 1.90x | 0.73x | 4 of 5 |
| x25519-keygen | 86.36 µs | 36.94 µs | 45.73 µs | 1.24x | 0.53x | 4 of 5 |
| ed25519-keygen | 88.59 µs | 38.98 µs | 49.05 µs | 1.26x | 0.55x | 4 of 5 |
| ed25519-verify | 267.37 µs | 178.83 µs | 231.03 µs | 1.29x | 0.86x | 5 of 5 |
| ed25519-sign | 88.45 µs | 36.29 µs | 46.65 µs | 1.29x | 0.53x | 5 of 5 |
| p256-ecdh | 278.97 µs | 252.20 µs | 264.15 µs | 1.05x | 0.95x | 4 of 5 |
| p256-keygen | 57.08 µs | 53.12 µs | 44.59 µs | 0.84x | 0.78x | 5 of 5 |
| p256-ecdsa-verify | 260.95 µs | 250.01 µs | 228.33 µs | 0.91x | 0.87x | 5 of 5 |
| p256-ecdsa-sign | 84.34 µs | 86.87 µs | 66.04 µs | 0.76x | 0.78x | 5 of 5 |
| mlkem768-keygen | - | 64.09 µs | 67.42 µs | 1.05x | - | 5 of 5 |
| mlkem768-encaps | - | 66.97 µs | 67.68 µs | 1.01x | - | 5 of 5 |
| mlkem768-decaps | - | 74.45 µs | 43.15 µs | 0.58x | - | 5 of 5 |
| argon2id-16MiB-t1-p1 | - | - | 40.83 ms | - | - | 5 of 5 |

Argon2id is timed against RustCrypto here (there is no ring or aws-lc-rs Argon2): 16 MiB, one pass, one lane, 40.83 ms for rind.

## Cortex-A72 and the narrow multiplier schedules (steelhead99x/rind#82)

Before steelhead99x/rind#82, rind ran s2n-bignum's `_alt` schedules on every core, and on this board X25519 ECDH took 1.90x as long as aws-lc-rs, X25519 keygen 1.23x, and Ed25519 keygen, sign, and verify 1.26 to 1.29x. rind beat ring on every one of those rows. steelhead99x/rind#82's `narrow_part()` lists `0xd08`, `0xd0b`, and `0xd0c`, and on this board the default build takes the narrow schedules: its times equal the forced-narrow times to within 0.1 percent and differ from forced-wide by 1.3 to 2.0x.

| Operation | aws-lc-rs | rind default | rind narrow forced | rind wide forced | default / aws-lc-rs | wide / aws-lc-rs | wide / narrow |
|---|---:|---:|---:|---:|---:|---:|---:|
| x25519-ecdh | 114.66 µs | 109.73 µs | 109.78 µs | 217.91 µs | 0.96x | 1.90x | 1.98x |
| x25519-keygen | 36.88 µs | 33.67 µs | 33.68 µs | 45.52 µs | 0.91x | 1.23x | 1.35x |
| ed25519-keygen | 38.80 µs | 37.20 µs | 37.19 µs | 49.23 µs | 0.96x | 1.27x | 1.32x |
| ed25519-verify | 178.82 µs | 165.75 µs | 165.74 µs | 230.91 µs | 0.93x | 1.29x | 1.39x |
| ed25519-sign | 36.33 µs | 34.59 µs | 34.59 µs | 46.70 µs | 0.95x | 1.29x | 1.35x |
| p256-ecdh | 251.62 µs | 264.14 µs | 264.18 µs | 264.16 µs | 1.05x | 1.05x | 1.00x |
| p256-keygen | 52.91 µs | 44.66 µs | 44.64 µs | 44.77 µs | 0.84x | 0.85x | 1.00x |
| p256-ecdsa-verify | 249.42 µs | 228.41 µs | 228.42 µs | 228.34 µs | 0.92x | 0.92x | 1.00x |
| p256-ecdsa-sign | 86.43 µs | 65.64 µs | 65.66 µs | 65.69 µs | 0.76x | 0.76x | 1.00x |

- steelhead99x/rind#82 closes the gap on the A72. X25519 ECDH goes from 1.90x to 0.96x of aws-lc-rs (218 to 110 us, 1.99x faster), keygen from 1.23x to 0.91x, and Ed25519 from 1.26 to 1.29x to 0.93 to 0.96x. Narrow is 1.32 to 1.98x faster than wide here.
- P-256 does not move between the three variants (all within 0.5 percent), so on this board P-256 does not depend on the schedule. Its remaining gap is ECDH, 1.05x of aws-lc-rs (264 against 252 us), while keygen, ECDSA sign, and ECDSA verify are 0.76 to 0.92x.

## Argon2id, NEON fill off against on (steelhead99x/rind#163)

`main` (`6efcb465`) against steelhead99x/rind#163 (`fc4d7df0`), t=3, p=1, median of 5 rounds of the median of 9 runs each, with RustCrypto's `argon2` timed beside it:

| Memory | rind, main | rind, steelhead99x/rind#163 | steelhead99x/rind#163 over main | RustCrypto (main run) | RustCrypto (steelhead99x/rind#163 run) |
|---|---:|---:|---:|---:|---:|
| 8 MiB | 50.09 ms | 44.67 ms | 1.12x faster | 49.41 ms | 49.33 ms |
| 64 MiB | 482.4 ms | 453.1 ms | 1.065x faster | 512.8 ms | 501.9 ms |

The control agrees within 1.001x at 8 MiB and 1.022x at 64 MiB (a 2 percent drift, so the 64 MiB figure is a little less certain). steelhead99x/rind#163 takes rind from 1.01x of RustCrypto's time to 0.91x at 8 MiB, and from 0.94x to 0.90x at 64 MiB.

## AES-GCM against ChaCha20-Poly1305

With no AES or PMULL instruction, rind's AES-GCM runs vpaes and a NEON GHASH, and ChaCha20-Poly1305 runs NEON. Seal, rind, median of 5. The 32 B row is under a 32 B AAD, and the 64 B to 512 B rows are Criterion's `quic-` rows (13 B AAD):

| Size | AES-128-GCM | AES-256-GCM | ChaCha20-Poly1305 | AES-128-GCM / ChaCha |
|---|---:|---:|---:|---:|
| 32 B | 1245 ns (26 MB/s) | 1516 ns (21 MB/s) | 808 ns (40 MB/s) | 1.54 |
| 64 B | 1719 ns (37 MB/s) | 2124 ns (30 MB/s) | not benched | |
| 128 B | 2826 ns (45 MB/s) | 3534 ns (36 MB/s) | 978 ns (131 MB/s) | 2.89 |
| 256 B | 5041 ns (51 MB/s) | 6329 ns (40 MB/s) | 1383 ns (185 MB/s) | 3.65 |
| 512 B | 9460 ns (54 MB/s) | 11935 ns (43 MB/s) | 2525 ns (203 MB/s) | 3.75 |
| 1200 B | 21549 ns (56 MB/s) | 27203 ns (44 MB/s) | 5059 ns (237 MB/s) | 4.26 |
| 16 KB | 284240 ns (58 MB/s) | 359270 ns (46 MB/s) | 64055 ns (256 MB/s) | 4.44 |

ChaCha20-Poly1305 is 1.5x faster at 32 B and 4.4x at 16 KB, so a TLS or QUIC peer on a Pi 4 should prefer it, which `rind-rustls` and `rind-dimpl` already do where `has_aes_hardware()` is false.

## AES-GCM size thresholds

A size sweep from 16 B to 16 KB (a separate binary, one pass per size, core 3) puts rind at 0.93 to 0.99 of aws-lc-rs up to 192 B, 1.00 at 256 B, and 1.01 to 1.02 from 384 B to 16 KB, for AES-128 and AES-256 both (aws-lc-rs and ring track within 1 percent of each other). The curve is monotone, with no step at the short-path limits (`SHORT_SEAL_BLOCKS` 15 blocks, 240 B, and `SHORT_OPEN_BLOCKS` 31 blocks, 496 B), so the current vpaes plus NEON GHASH thresholds are at or near optimal for the A72, and the only gap left is the 1.02 on large buffers. The raw rows are in steelhead99x/rind-results#84.

## Gaps left

No row is over 1.05x of aws-lc-rs after steelhead99x/rind#82, and none outside steelhead99x/rind#82, steelhead99x/rind#128, steelhead99x/rind#188, steelhead99x/rind#163, steelhead99x/rind#187, steelhead99x/rind#141, and steelhead99x/rind#193 is over 1.05x. The two at the edge are P-256 ECDH (1.05x) and ML-KEM-768 keygen (1.05x: 67.4 against 64.1 us, with encaps 1.01x and decaps 0.58x). AES-GCM is 1.01 to 1.02x at 1200 B and larger. They are noted here and not fixed.

## Caveats

- ondemand at 1.8 GHz, not a fixed clock, and a second worker on core 0 for most of the baseline. Compare ratios, not absolute times.
- The sticky `0x80000` bit and the 71 to 73 degree readings in baseline rounds 1 to 5 are the reason the median of 5, not a single round, is used.
- One board, one kernel. Valgrind, ctgrind, and the native test lane were not part of this run.
