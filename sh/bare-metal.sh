#!/usr/bin/env bash
# Lint rind's library for bare-metal targets (`target_os = "none"`), where it
# builds without std, as `just bare-metal` and `just check`'s cross module run
# it. Compile only: nothing here links a program, runs one, or checks timing
# on these cores.
set -euo pipefail

cd "$(dirname "${BASH_SOURCE[0]}")/.."

# getrandom has no source on these targets until the program names one, which
# a library build cannot, so its custom backend stands in.
custom='--cfg getrandom_backend="custom"'

# lint TARGET: debug, whose `debug_assertions` code release leaves out, and
# release, each with and without `wipe`.
lint() {
    local target=$1
    local flags
    flags="CARGO_TARGET_$(tr 'a-z.-' 'A-Z__' <<<"$target")_RUSTFLAGS"
    for profile in dev release; do
        for features in "" wipe; do
            env "$flags=$custom" cargo clippy -p rind --lib --locked --target "$target" \
                --profile "$profile" --features "$features" -- --deny warnings
        done
    done
}

# ARMv6-M (Cortex-M0+, the RP2040) and RV32IMC (the ESP32-C3) have no
# compare-and-swap, so they build `reuse_cache_without_cas`; ARMv7E-M
# (Cortex-M4 and M7, such as the nRF52840) has it, on the portable backend;
# and bare-metal x86_64 gets the portable backend rather than its std-only
# assembly one.
for target in thumbv6m-none-eabi riscv32imc-unknown-none-elf thumbv7em-none-eabihf x86_64-unknown-none; do
    lint "$target"
done
