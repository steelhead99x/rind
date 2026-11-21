# [M] An ESP32-C6 firmware times rind and seals sensor readings, and its log becomes a scrubbed result

## Goal

An ESP32-C6 runs rind's known-answer checks and times each algorithm on the chip, shows its state on the board's LED, prints the result over USB-Serial-JTAG, and `admin/esp32c6-bench-ingest` turns that log into scrubbed JSON in `admin/bench-report`'s row shape. A second example signs and seals a sensor's readings with Ed25519 and ChaCha20-Poly1305 behind a `Sensor` trait, so the board's sensor, which is not identified yet, is one `impl` away. Nothing in this quest has run on the board: its host half is built and tested, and its board half is a list of commands.

## Plan

Drafted 2026-11-20 (Claude), on [the riscv32imac build and size quest](/quest/m2/bench/esp32-c6-riscv32.md)'s crate.

- `admin/esp32c6/src/bench.rs` times an operation over rounds and iterations on a `Clock` trait, and prints `RIND-BENCH v1 <bench-report operation> median_ns=... min_ns=... max_ns=... rounds=... iters=...`. The statistics are unit-tested with fake clocks.
- `admin/esp32c6/src/sensor.rs` is the example: `Sensor`, `Reading`, `SyntheticSensor` (a fixed ramp, labelled synthetic), `DeviceKeys` (HKDF-SHA256 from one 32-byte secret), `Sealer` and `Opener`. A packet is `version | seq | ChaCha20-Poly1305(reading, aad = version | seq) | Ed25519 over everything before`, the nonce is the sequence number XORed into a derived IV, and the opener refuses a replayed or older number. Unit tests cover the round trip, every single-byte change, replay, a wrong key, a short packet, and counter exhaustion, and the `sensor` check runs it on riscv32imac under qemu.
- `admin/esp32c6/firmware/` is the board image (esp-hal 1.2, esp-println over USB-Serial-JTAG, esp-alloc): blue LED while it runs, green when every check passed, red on a failure or a panic, a WS2812 on GPIO8 (ESP32-C6-DevKitC-1) and a plain active-low LED on GPIO15 (XIAO ESP32-C6) both driven because the board is unidentified. It repeats its summary every five seconds so a monitor opened late still sees it. `admin/esp32c6-riscv32 firmware` builds it and prints the flash command; nothing flashes from the repository's scripts.
- `admin/esp32c6-bench-ingest LOG --out FILE` keeps the first complete summary, refuses a panic, a failed check, a malformed or disagreeing summary and out-of-order min/median/max, drops boot output, and refuses to write if a MAC address, host path, serial port, address, or email survives. Its `selftest` runs in the dev shell.
- On the board, run (port from `espflash list-ports`; a port you do not own is not yours): `admin/esp32c6-riscv32 firmware`, `espflash flash --port PORT --chip esp32c6 <elf>`, then read the serial log for about 60 s into a file and run `admin/esp32c6-bench-ingest`. Record temperature and the supply (USB or battery) with the log; the firmware does not read the chip's temperature sensor yet.
- Left out, and why: ML-KEM, ML-DSA, and P-256 timing (a run takes seconds each and `qemu` shows ML-DSA needs 85 KB of heap, so size the heap first), and an `admin/bench-report` host for the C6, which has no controls (aws-lc-rs and ring do not build for it).

## Waiting

- steelhead99x: identify the sensor board ("sensor wave") and its bus. Options: (A) a part number or photo, then write its driver behind `Sensor`; (B) keep the synthetic sensor until the board is wired; (C) drop the sensor example. Recommendation: A.
- steelhead99x: run the firmware on the board and send the log. Options: (A) the commands above; (B) grant this agent the serial port for a run. Recommendation: A.
