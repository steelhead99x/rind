# [S] Time HMAC-SHA256 on a real STM32F411

## Goal

A `thumbv7em-none-eabihf` build of rind uses the portable backend without `--cfg rind_portable`, and a measurement on a real STM32F411 (Cortex-M4F) records cycles, microseconds at 100 MHz, and flash for HMAC-SHA256 truncated to 4 bytes over a 14-byte frame.

## Plan

M-profile is Thumb-only and has no NEON, so the A32 assembly backend does not assemble there. `rind/build.rs` already selects the portable backend for those triples, including `thumbv7em-none-eabihf`, `thumbv7m-none-eabi`, and `thumbv8m` / `thumbv8.1m`. That landed on this fork in [steelhead99x/rind#154](https://github.com/steelhead99x/rind/pull/154). `--cfg rind_portable` stays a test-only override, as `build.rs` documents.

Checked while adding this quest, rustc 1.100.0:

```
RUSTFLAGS='--cfg getrandom_backend="custom"' cargo build -p rind --lib --no-default-features --locked --target thumbv7em-none-eabihf
```

Exit 0, `Finished dev profile in 1m 10s`. The build script set `rind_backend="portable"`, `rind_limb="32"`, and `rind_reg_asm`, and did not set `rind_std`. `rind_reg_asm` is the portable MD5 barrier, which the `arm` arch already allows. The custom getrandom cfg is the stand-in `sh/bare-metal.sh` uses, because `target_os = "none"` has no entropy source until the program names one. The rlib does not need a global allocator.

Host x86_64, from the build script output of `cargo test -p rind-rustls --locked --all-targets` in the same tree: `rind_backend="x86_64"`, `rind_limb="64"`, and `rind_std`. The M-profile check is not on that path.

The estimate to confirm, scaled from rind's portable backend on an nRF52840 (Cortex-M4F, DWT cycles) and not yet run on an F411: pre-keyed HMAC-SHA256 of a 14-byte frame is about 10k cycles, about 100 us at 100 MHz, and HMAC-SHA256 tag and verify is about 8 KB of flash. The F411's flash wait states differ, so treat that as plus or minus 30 percent until this board is timed. The frame is the 14-byte auth input (the link sketch is `"rc1" || direction || counter || frame`). The tag is the first 4 bytes of HMAC-SHA256.

When the board is here: time that operation with the cycle counter, and record linked `.text` against an empty image. Do not open a pull request on kixel-ai/rind for this. The selection is already on the fork, and PLATFORMS.md already names the portable backend for this target.

## Waiting

- Maintainer (PC): an STM32F411 is available to flash and time HMAC-SHA256. An agent cannot run the chip. Check: this quest's Plan records the board's cycle count, microseconds at 100 MHz, and flash bytes.

## Related

- [steelhead99x/rind#154](https://github.com/steelhead99x/rind/pull/154) - the build-script change that selects the portable backend on M-profile
