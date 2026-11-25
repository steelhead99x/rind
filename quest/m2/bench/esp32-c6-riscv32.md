# [M] rind builds, passes its known answers, and is sized on riscv32imac, the ESP32-C6's core

## Goal

rind's portable backend on `riscv32imac` (the ESP32-C6, a 160 MHz RISC-V core with no hardware SHA-512 or AES that rind uses) is known to build, to give the published answer for each algorithm an embedded user reaches for, and to cost a stated amount of code, static RAM, stack, and heap per algorithm. All of it is measured without the board: a cross build, a run under `qemu-riscv32` (user mode), and static section sizes. No time and no board number is claimed until the board runs it (the bench harness quest, `esp32-c6-bench`).

## Plan

Drafted 2026-11-20 (Claude, for the owner's ESP32-C6): mirror what [the ESP-IDF SHA-2 quest](/quest/m4/verified/rolled-sha2-esp.md) and `admin/esp32s3-sha256-layout` did for Xtensa, without the layout checks the C6 does not need yet (it has no IRAM placement here; rind's SHA-2 on `riscv32imac` is the portable aws-lc port).

- `admin/esp32c6-riscv32 build` cross-builds the `rind` library for `riscv32imac-unknown-none-elf`.
- `admin/esp32c6/` is a standalone crate (its own workspace) of known-answer functions, one per algorithm and one Cargo feature each: SHA-256, SHA-512, SHA3-256, HMAC-SHA256, HKDF-SHA256, ChaCha20-Poly1305, AES-128-GCM, AES-256-GCM, X25519, Ed25519, ML-KEM-768, ML-DSA-65, ECDSA P-256. The vector ones use RFC and NIST vectors; the others check a round trip and a rejected change. `cargo test` runs them on the host too, so every vector is checked on a second CPU.
- `qemu-kat` runs them on riscv32imac in `qemu-riscv32` with no libc: its own `_start` and `ecall` syscalls, a painted stack (peak stack is the distance from the caller's sp to the lowest dirty byte; a run that dirties nothing painted reports the 256-byte unpainted guard, the floor of every reading; it is a high-water estimate of bytes written, so stack reserved but never written does not show) and a counting allocator (peak heap). Both are properties of the code, not of the emulator.
- `admin/esp32c6-riscv32 size` builds each algorithm alone and reports its code (text and rodata) over the empty harness, its static RAM, and its stack and heap from the run. An algorithm that shares code with another (SHA-512 under Ed25519) shows only what it adds over the harness, not what it adds over the others.
- Not measured, on purpose: speed (qemu's clock is not the chip's), flash placement, and the ESP-IDF target (`riscv32imac-esp-espidf` needs ESP-IDF's toolchain, which this host lacks).
- The flake's Rust targets lack `riscv32imac-unknown-none-elf`, so the script needs a toolchain that has it. Adding the target to `flake.nix` and a CI job is the follow-up, left to the maintainer.

## Waiting

- Maintainer: add `riscv32imac-unknown-none-elf` and `qemu-user` to the dev shell and a path-filtered workflow that runs `admin/esp32c6-riscv32 test`. Options: (A) both now; (B) after the board numbers exist; (C) leave it a local script. Recommendation: B.
