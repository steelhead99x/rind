# [L] rind builds without std, down to a Cortex-M0+

## Goal

The rind library compiles as `#![no_std]` with `alloc` on the portable backend's bare-metal targets, `thumbv6m-none-eabi` (Cortex-M0+, the RP2040) the smallest, and its operations run there with the same results as on the hosted targets. A `std` feature, on by default, keeps today's API and behaviour for every existing consumer. Every PR compiles the library for `thumbv6m-none-eabi`, as it does for wasm32, and a small embedded runner times rind's primitives on an RP2040 so the report can show a microcontroller row.

Non-goals: the adapters (rind-ring, rind-rustls, rind-aws-lc-rs and the rest) without std, and speed on the cold tier, which [m3's cold-speed epic](/quest/m3/cold-speed/README.md) owns.

## Plan

Planned on 2026-11-12 from an attempted RP2040 build at a4759c48 (rustc 1.99.1). Nothing below is decided yet; each ✅ is the proposal, for the maintainer to settle.

- Milestone: ✅ m3, since no consumer has asked for bare metal and m3 holds work waiting on one (rejected: m2 adoption, beside the finished targets epic; m4).
- Scope: ✅ library only, `std` default-on (rejected: no_std without alloc, which would need rewriting about 80 modules' `Vec`/`Box`/`String` use, including ML-DSA, RSA, and ASN.1).
- CI: ✅ compile-only for `thumbv6m-none-eabi` on every PR, with and without `wipe`, as wasm32 is (rejected: tests under qemu's Cortex-M0 machine, which a later quest can add).

What fails today, from `cargo build -p rind --release --target thumbv6m-none-eabi`:

- getrandom 0.4.3 refuses the target unless the final binary sets `--cfg getrandom_backend="custom"` and supplies the custom function. With that set, rind itself fails with 1672 errors, the first `error[E0463]: can't find crate for std`. Nearly all the rest are the std prelude missing (`Result`, `Option`, `derive`, `vec!`, and so on), so most of the change is `#![cfg_attr(not(feature = "std"), no_std)]`, `extern crate alloc`, and `alloc::` imports.
- std in non-test code:
  - `rind/src/low/cpu.rs:121`: `std::thread_local!` holding `DIT_GUARDS`, the count of live `cpu::Dit` guards. Only Apple's aarch64 sets DIT, so on the portable backend it can be a no-op, with `Dit` kept as a zero-sized type.
  - `rind/src/low/entry.rs:8`: `std::thread_local!` holding `HELD`, compiled only with `debug_assertions` outside tests. Without std, use a plain static counter or drop `Entry::assert_held`'s check.
  - `rind/src/low/x86_64/{sha1_mux,sha256_mux,sha512}.rs`: `std::sync::OnceLock` for the dispatch choice. These aren't on the bare-metal path, but the crate-wide `no_std` needs them on core atomics or behind `std`.
  - `rind/src/low/abi.rs:23`, `:287`: `std::sync::Mutex`, which compiles only under `cfg(test)` (`rind/src/low/mod.rs`), so it does not block the library.
- Compare-and-swap: `rind/src/low/generic/reuse_cache.rs:44`, `:49`, `:73` call `fetch_max` and `compare_exchange` on an `AtomicU8`, and the portable backend that thumbv6m runs uses them. ARMv6-M has no exclusive loads or stores, so those methods don't exist there. Use `portable-atomic` with its `critical-section` feature, which the binary implements (single-core RP2040: interrupts off), or build that cache single-threaded on targets without CAS. Plain atomic loads and stores, such as `verify_cpu_features`' `AtomicBool` in `low/cpu.rs`, already work.
- Randomness: rind's RNG calls `getrandom::fill` (`rind/src/mid/rng.rs:21`). Leave the source to the binary through getrandom's custom backend, and document it in PLATFORMS.md (on the RP2040, its ring oscillator or an external TRNG).

What already builds for `thumbv6m-none-eabi`, at the versions rind pins: every portable-backend dependency: curve25519-dalek 5 (`default-features = false`, `precomputed-tables`), fiat-crypto 0.3, libcrux-sha2 0.0.9, libcrux-poly1305 0.0.7, libcrux-hacl-rs 0.0.6 with `alloc`, subtle, rand_core 0.10, and getrandom 0.4 with the custom backend. ring 0.17 is `#![no_std]` too, so a ring user on bare metal can't move to rind today. Whether ring builds for thumbv6m wasn't checked; aws-lc-rs doesn't build without an OS.

Constant time: ARMv6-M's `muls` is 32×32→32 and fixed-time in both of Arm's implementation options (1 or 32 cycles), so every 32×32→64 product the portable backend forms becomes a call to compiler-builtins' `__aeabi_lmul`. On rustc 1.99.1 that routine is four `muls` and an `adds`/`adcs` carry chain with no branch, unlike libgcc's routine of the same name ([BearSSL's table](https://www.bearssl.org/ctmul.html)). Add `thumbv6m-none-eabi` to `admin/ct-vartime`'s release builds so it keeps checking that.

What competitors build for thumbv6m today, from compile-only `#![no_std]` builds at `rind-bench`'s versions with default features off:

- RustCrypto's sha2 0.11.1, hmac 0.13.0, aes-gcm 0.11.1, chacha20poly1305 0.11.0, and p256 0.14.0 (`ecdsa`), and curve25519-dalek 5.0.0, x25519-dalek 3.0.0, and ed25519-dalek 3.0.0, build for `thumbv6m-none-eabi`, `thumbv7em-none-eabihf`, `thumbv8m.main-none-eabihf`, `riscv32imc-unknown-none-elf`, and `riscv32imac-unknown-none-elf`, with no randomness backend or CAS.
- ring 0.17.14 needs a C cross-compiler and getrandom 0.2's `custom` feature. With both, its ARM assembly (`crypto/curve25519/asm/x25519-asm-arm.S`) does not assemble for thumbv6m or thumbv7em under `arm-none-eabi-gcc` 15.3.
- aws-lc-rs 1.19.0's C build expects an OS (`pthread_rwlock_t`, `clock_gettime`).
- rustls 0.23.46 builds without a provider, and with rustls-rustcrypto, on the targets with CAS. On thumbv6m and riscv32imc it needs CAS (once_cell's `race`) and an atomic `Arc` (`alloc::sync`), which rustls leaves to forks.
- So rind's goal on bare metal is parity with the RustCrypto and dalek crates, which rind's portable backend already builds on.

Other targets with the same constraints: the Cortex-M0/M0+ parts (STM32G0, STM32L0, STM32F0, nRF51, SAMD21) share the RP2040's target and limits. ESP32-C3 (`riscv32imc`) also lacks CAS. Cortex-M4/M7/M33 (`thumbv7em`, `thumbv8m.main`; e.g. EFR32MG24), RP2350's Hazard3, and ESP32-C6/H2 (`riscv32imac`) have CAS and lack only std and an RNG source. Multiply timing differs:

- Cortex-M4/M7: `umull` is single-cycle, fixed. Cortex-M33 (e.g. EFR32MG24): `umull` is present, but Arm documents no cycle count; its TRM names early termination only for the divider, so measure before claiming constant time.
- Cortex-M3: `umull` finishes early on small, zero, or power-of-two operands, so the 32-bit limb code is not constant time there.
- Hazard3: constant time only with its `MUL_FAST` and `MULH_FAST` options.
- Espressif's RISC-V and Xtensa cores: multiply timing is undocumented.
- riscv32 without M: software multiply loops exit early.

MSP430 and AVR are out of scope (16- and 8-bit, a few KB of RAM).

Proposed for the decision above:

- CI compile-checks `thumbv6m-none-eabi`, `thumbv7em-none-eabihf`, `thumbv8m.main-none-eabihf`, `riscv32imc-unknown-none-elf`, and `riscv32imac-unknown-none-elf`.
- PLATFORMS.md's multiplier list gains the Cortex-M3, riscv32 without M, and the undocumented cores.
- Benchmarks run on an RP2040, an RP2350 (both cores), an ESP32-C3, and a Cortex-M4F part.

Embedded runner:

- A `rind-bench-embedded` workspace member (unpublished, excluded from host `cargo bench`) built for `thumbv6m-none-eabi` with `embassy-rp` or `rp2040-hal`. It times rind's operations with the RP2040's 1 MHz timer, or with SysTick at the core clock (the M0+ has no DWT cycle counter). It reports cycles per operation and ns per operation at 125 MHz over USB serial or defmt. Start with SHA-256, SHA-512, HMAC-SHA256, ChaCha20-Poly1305 and AES-128-GCM at 64 B and 1 KiB, X25519, Ed25519 sign and verify, and P-256 ECDSA sign and verify. Leave out whatever doesn't fit in 264 KB of RAM.
- Compare against libraries that build for the target: RustCrypto's crates and curve25519-dalek / ed25519-dalek, the same ones `rind-bench` uses on the hosts.
- `admin/bench-report` gains no RP2040 host: results come from a flashed board, so their JSON is collected by hand and rendered as a separate table, like the nightly's rows.

Guidance:

- Keep "exactly one backend compiles per architecture": thumbv6m and the other `*-none-*` targets run the portable backend, chosen by `rind/build.rs` as now.
- [rind needs no runtime CPU check](/quest/m2/api/cpu-check.md) deletes `verify_cpu_features` and its atomic; if it lands first, there is one less thing to port.
- Update PLATFORMS.md, README's Limitations, and ARCHITECTURE.md's `cpu` line. Record new workarounds in UPSTREAM.md.

## Waiting

- Maintainer: choose the milestone. Recommendation: m3, because no consumer has asked for bare metal and m3 holds work waiting on one. Rejected: m2 adoption, beside the finished targets epic; m4. An agent cannot reorder the milestones. Clear it by marking the Plan's milestone line decided.
- Maintainer: choose the scope. Recommendation: the rind library only, with `std` on by default. Rejected: `no_std` without `alloc`, which would rewrite the `Vec`, `Box`, and `String` use in about 80 modules, including ML-DSA, RSA, and ASN.1. An agent cannot choose the supported surface. Clear it by marking the Plan's scope line decided.
- Maintainer: choose what CI runs. Recommendation: compile-only for `thumbv6m-none-eabi` on every PR, with and without `wipe`, as wasm32 is. Rejected: tests under qemu's Cortex-M0 machine, which a later quest can add. The Plan also proposes compile-checks for `thumbv7em-none-eabihf`, `thumbv8m.main-none-eabihf`, `riscv32imc-unknown-none-elf`, and `riscv32imac-unknown-none-elf`. An agent cannot add a gate to every PR. Clear it by marking the Plan's CI line decided.
