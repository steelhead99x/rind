# X-Wing against libcrux-kem and RustCrypto on hosts outside the report

`admin/bench-report` times only the hosts in its `HOSTS` table (`nixos`, `desktop`, `nixos2`, `kixtop`, `ovh-iad`, `ovh-sea`), and `render` ignores any other host's data, so the X-Wing rows of `BENCHMARKS.md` stay empty until `collect` runs on those hosts. These are the X-Wing rows of `rind-bench/benches/xwing.rs` measured on five machines the report does not cover, as the indicative numbers the claim lacked. They are not the report's, and nothing in `benchmarks/data` or `BENCHMARKS.md` uses them.

## Method

- Commit `71f8af64` (the claim head). `rind-bench/benches/xwing.rs` unchanged, built as a copy in a two-member workspace (`rind` and one bench crate with only criterion, libcrux-kem 0.0.10, x-wing 0.1.1, and getrandom), because `rind-bench` does not build on the Pi 5 (openssl-sys finds no headers there), on armv7 cross builds, or on a host with no network. On the Ryzen 7 255 the full `rind-bench --bench xwing` binary was used. Both run the same `agree()` check of rind against libcrux-kem and RustCrypto before timing.
- Interleaved A/B: each round times rind, libcrux-kem, and RustCrypto for one operation in an order that rotates by one each round, then rind again as the control, all with `taskset` on one core, criterion `--warm-up-time 1 --measurement-time 3` (`--measurement-time 2` on the laptop). A round is kept for an operation when its two rind times are within 1.02 of each other, and discarded otherwise. Each cell is the median of the kept rounds' criterion central estimates over the first 5 rounds (the first 3 on the laptop).
- Each row does what a protocol does with one key, as the bench's header says: keygen yields the encapsulation key's bytes; encaps parses a received key and encapsulates; decaps parses a received ciphertext and decapsulates.

## Results

| Host | Core and clock | Operation | rind | libcrux-kem | RustCrypto `x-wing` | Fastest other over rind | Kept rounds |
|---|---|---|---:|---:|---:|---:|---|
| Ryzen 7 255 (Zen 4) | 5, performance, about 3.3 to 4.9 GHz | keygen | 9.08 µs | 48.72 µs | 64.82 µs | 5.36x | 5 of 5 |
| Ryzen 7 255 (Zen 4) | 5, performance, about 3.3 to 4.9 GHz | encaps | 17.88 µs | 78.84 µs | 111.11 µs | 4.41x | 5 of 5 |
| Ryzen 7 255 (Zen 4) | 5, performance, about 3.3 to 4.9 GHz | decaps | 14.69 µs | 95.27 µs | 178.03 µs | 6.49x | 5 of 5 |
| Raspberry Pi 5 (Cortex-A76) | 3, performance, held at 1.5 GHz | keygen | 95.37 µs | 374.92 µs | 471.40 µs | 3.93x | 5 of 5 |
| Raspberry Pi 5 (Cortex-A76) | 3, performance, held at 1.5 GHz | encaps | 299.46 µs | 659.27 µs | 818.43 µs | 2.20x | 5 of 5 |
| Raspberry Pi 5 (Cortex-A76) | 3, performance, held at 1.5 GHz | decaps | 232.21 µs | 751.45 µs | 1.056 ms | 3.24x | 5 of 5 |
| Jetson Orin Nano (Cortex-A78AE) | 3, schedutil, 1.1 GHz, 15 W mode | keygen | 52.58 µs | 174.10 µs | 213.29 µs | 3.31x | 5 of 5 |
| Jetson Orin Nano (Cortex-A78AE) | 3, schedutil, 1.1 GHz, 15 W mode | encaps | 112.67 µs | 259.78 µs | 328.83 µs | 2.31x | 5 of 5 |
| Jetson Orin Nano (Cortex-A78AE) | 3, schedutil, 1.1 GHz, 15 W mode | decaps | 80.93 µs | 338.39 µs | 468.52 µs | 4.18x | 5 of 5 |
| Raspberry Pi 2 B (Cortex-A7) | 3, performance (restored to ondemand), 900 MHz | keygen | 1.258 ms | 3.168 ms | 2.786 ms | 2.21x | 3 of 5 |
| Raspberry Pi 2 B (Cortex-A7) | 3, performance (restored to ondemand), 900 MHz | encaps | 2.369 ms | 5.357 ms | 4.878 ms | 2.06x | 4 of 5 |
| Raspberry Pi 2 B (Cortex-A7) | 3, performance (restored to ondemand), 900 MHz | decaps | 1.560 ms | 6.906 ms | 7.319 ms | 4.43x | 5 of 5 |
| Core Ultra 9 275HX, provisional | 11, shared, busy | keygen | 24.92 µs | 98.88 µs | 109.03 µs | 3.97x | 1 of 3 |
| Core Ultra 9 275HX, provisional | 11, shared, busy | encaps | 59.55 µs | 166.05 µs | 209.30 µs | 2.79x | 1 of 3 |
| Core Ultra 9 275HX, provisional | 11, shared, busy | decaps | no clean round | no clean round | no clean round | - | 0 of 3 |

## Discarded rounds

- Ryzen 7 255, Pi 5, Jetson: none. A first Ryzen run, while other jobs were building on the host, was discarded whole (load average 8 to 9, rind's control disagreed by up to 40%); the rerun waited for a load average under 3 and kept every round.
- Pi 2 B: keygen rounds 1 and 2, encaps round 3.
- Laptop: keygen and encaps rounds 1 and 2, every decaps round. The laptop ran at a load average of 40 to 60 on 24 logical CPUs for the whole run, so its two kept cells are single rounds and provisional.

## Caveats

- The Pi 5 was held at 1.5 GHz (not its 2.4 GHz maximum) with `performance` set, and a virtual machine of another job ran on a different core. The Jetson's governor is `schedutil` and could not be changed without a password, so it sat at 1.1 GHz in rounds 2 to 8. The Pi 2 B's governor was set to `performance` for the run and restored to `ondemand`. Compare ratios across these rows, not absolute times.
- libcrux-kem follows draft 06 of X-Wing and RustCrypto the final draft; the bench's `agree()` checks the three give the same secret before timing.
- Missing: the report's own hosts and the classes the claim notes name, Apple silicon, Zen 5, Intel server, and Graviton.
