#!/usr/bin/env bash
# Lint rind's library for bare-metal targets (`target_os = "none"`), where it
# builds without std, as `just bare-metal` and `just check`'s cross module run
# it. `xtensa` lints it for the ESP32's Xtensa targets instead, which are tier
# 3 and need espup's toolchain (`ESP_TOOLCHAIN`, by default `esp`), as `just
# xtensa` and the nightly build.yml run it. Compile only: nothing here links a
# program, runs one, or checks timing on these cores.
#
# Usage: sh/bare-metal.sh [xtensa]
set -euo pipefail

if (( $# > 1 )) || [[ "${1:-}" != "" && "$1" != xtensa ]]; then
    echo "Usage: $0 [xtensa]" >&2
    exit 2
fi

cd "$(dirname "${BASH_SOURCE[0]}")/.."

# getrandom has no source on these targets until the program names one, which
# a library build cannot, so its custom backend stands in.
custom='--cfg getrandom_backend="custom"'
cargo=(cargo)

# lint TARGET [CLIPPY-ARGS...]: debug, whose `debug_assertions` code release
# leaves out, and release, each with and without `wipe`.
lint() {
    local target=$1
    shift
    local flags
    flags="CARGO_TARGET_$(tr 'a-z.-' 'A-Z__' <<<"$target")_RUSTFLAGS"
    for profile in dev release; do
        for features in "" wipe; do
            env "$flags=$custom" "${cargo[@]}" clippy "$@" -p rind --lib --locked --target "$target" \
                --profile "$profile" --features "$features" -- --deny warnings
        done
    done
}

# aws-lc builds for none of these, so rind-bench must leave it out of its
# dependencies there, as its benches leave out aws-lc-rs's rows.
no_aws_lc() {
    local target=$1
    local crates
    crates=$("${cargo[@]}" tree -p rind-bench -e normal,build,dev --locked --target "$target" \
        --prefix none --format '{p}')
    if grep -E '^aws-lc' <<<"$crates"; then
        echo "error: rind-bench depends on aws-lc for $target" >&2
        exit 1
    fi
}

if [[ "${1:-}" == xtensa ]]; then
    cargo=(cargo "+${ESP_TOOLCHAIN:-esp}")
    # Tier 3 ships no prebuilt standard library, so it is built from source:
    # the ESP32 (LX6) and ESP32-S3 (LX7) bare metal, then ESP-IDF's std. That
    # one is compiled, not linted: there clippy's `missing_const_for_thread_local`
    # flags thread-locals whose initializers are already `const`.
    # See UPSTREAM.md's "Clippy flags const thread-local initializers".
    for target in xtensa-esp32-none-elf xtensa-esp32s3-none-elf; do
        lint "$target" -Zbuild-std=core,alloc
    done
    "${cargo[@]}" check -Zbuild-std=std,panic_abort -p rind --lib --locked \
        --target xtensa-esp32s3-espidf
    no_aws_lc xtensa-esp32s3-espidf
    exit 0
fi

# ARMv6-M (Cortex-M0+, the RP2040) and RV32IMC (the ESP32-C3) have no
# compare-and-swap, so they build `reuse_cache_without_cas`; ARMv7E-M
# (Cortex-M4 and M7, such as the nRF52840) has it, on the portable backend;
# and bare-metal x86_64 gets the portable backend rather than its std-only
# assembly one.
for target in thumbv6m-none-eabi riscv32imc-unknown-none-elf thumbv7em-none-eabihf x86_64-unknown-none; do
    lint "$target"
done
no_aws_lc thumbv7em-none-eabihf
