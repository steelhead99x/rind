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
# curve25519-dalek's default on x86_64 is its AVX2 backend, chosen at run
# time. This target does not promise those registers are saved, so the lint
# builds the serial backend, as the portable constant-time jobs do. The
# library refuses the build without this cfg.
serial='--cfg curve25519_dalek_backend="serial"'

# lint TARGET [CLIPPY-ARGS...]: debug, whose `debug_assertions` code release
# leaves out, and release, each with and without `wipe`.
lint() {
    local target=$1
    shift
    local flags rustflags
    flags="CARGO_TARGET_$(tr 'a-z.-' 'A-Z__' <<<"$target")_RUSTFLAGS"
    rustflags=$custom
    if [[ $target == x86_64-unknown-none ]]; then
        rustflags+=" $serial"
    fi
    for profile in dev release; do
        for features in "" wipe; do
            env "$flags=$rustflags" cargo clippy "$@" -p rind --lib --locked --target "$target" \
                --profile "$profile" --features "$features" -- --deny warnings
        done
    done
}

# aws-lc builds for none of these, so rind-bench must leave it out of its
# dependencies there, as its benches leave out aws-lc-rs's rows.
no_aws_lc() {
    local target=$1
    local crates
    crates=$(cargo tree -p rind-bench -e normal,build,dev --locked --target "$target" \
        --prefix none --format '{p}')
    if grep -E '^aws-lc' <<<"$crates"; then
        echo "error: rind-bench depends on aws-lc for $target" >&2
        exit 1
    fi
}

# ARMv6-M (Cortex-M0+, the RP2040) and RV32IMC (the ESP32-C3) have no
# compare-and-swap, so they build `reuse_cache_without_cas`. ARMv7E-M
# (Cortex-M4 and M7, such as the nRF52840) has it, on the portable backend.
# A-profile `armv7a-none-eabi` and R-profile `armv7r-none-eabihf` keep the
# 32-bit ARM backend: bare metal never asks a kernel, so that backend's
# NEON and crypto paths stay off and the base assembly is what runs.
# Bare-metal aarch64, with hardware floating point and without it, gets the
# portable backend, as does bare-metal x86_64.
for target in \
    thumbv6m-none-eabi \
    riscv32imc-unknown-none-elf \
    thumbv7em-none-eabihf \
    armv7a-none-eabi \
    armv7r-none-eabihf \
    aarch64-unknown-none \
    aarch64-unknown-none-softfloat \
    x86_64-unknown-none; do
    lint "$target"
done
no_aws_lc thumbv7em-none-eabihf
