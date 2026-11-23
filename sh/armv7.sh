#!/usr/bin/env bash
# Build, lint, and test the armv7 targets, as `just armv7` runs it inside the
# flake's `armv7` dev shell. The gnueabihf tests run three times, to cover
# each of rind's armv7 tiers, under qemu-user or, on an aarch64 host that runs
# AArch32 code, natively for all but the Cortex-A15's.
set -euo pipefail

if [[ -z "${CARGO_TARGET_ARMV7_UNKNOWN_LINUX_GNUEABIHF_RUNNER:-}" ]]; then
    echo "error: run through 'just armv7', which enters the flake's armv7 dev shell" >&2
    exit 1
fi

cd "$(dirname "${BASH_SOURCE[0]}")/.."

# The bench and fuzz crates need C libraries built for the target.
packages=(-p rind -p rind-rustls -p rind-jsonwebtoken -p rind-object-store -p rind-rcgen -p rind-rand-core -p rind-ring -p rind-aws-lc-rs -p rind-dimpl -p rind-openmls -p rind-str0m)

# Android has no C toolchain here, so its build shows rind needs none. Only
# the tested target lints the tests, whose aws-lc-rs dev-dependency builds C.
android=armv7-linux-androideabi
cargo build "${packages[@]}" --locked --target "$android"
cargo clippy "${packages[@]}" --locked --target "$android" -- --deny warnings

target=armv7-unknown-linux-gnueabihf
cargo build "${packages[@]}" --locked --target "$target"
cargo clippy "${packages[@]}" --locked --target "$target" --all-targets -- --deny warnings

# Under qemu, so optimised, but keeping the checks a debug build has.
export CARGO_PROFILE_RELEASE_DEBUG_ASSERTIONS=true
export CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS=true

# The crypto extension's tier takes qemu's `max` CPU, which has it and so
# NEON. The NEON-denied tier hides NEON, and with it the extension, behind
# rind's software mask, leaving only the scalar paths. Each runs natively on
# an aarch64 host whose CPU can run it, such as GitHub's arm64 runners: arm64
# Linux refuses the 32-bit personality on a CPU without AArch32, such as
# Graviton 4 or a VM on Apple silicon, and under it /proc/cpuinfo lists the
# AArch32 features, which on a Raspberry Pi 4 lack the extension. The
# Cortex-A15 is ARMv7 with NEON but without the extension: its tier stays
# under qemu on every host, where an instruction from the extension faults.
# RIND_TEST_ARM_* fails a run on the wrong path.
native=(env -u CARGO_TARGET_ARMV7_UNKNOWN_LINUX_GNUEABIHF_RUNNER)
crypto=(env QEMU_CPU=max)
denied=(env QEMU_CPU=cortex-a15)
if [[ "$(uname -m)" == aarch64 ]] && features=$(setarch linux32 grep -m1 '^Features' /proc/cpuinfo 2>/dev/null); then
    echo "armv7: the NEON-denied tier runs natively" >&2
    denied=("${native[@]}")
    has_crypto=true
    for feature in aes pmull sha1 sha2; do
        [[ " ${features#*:} " == *" $feature "* ]] || has_crypto=false
    done
    if [[ "$has_crypto" == true ]]; then
        echo "armv7: the crypto extension's tier runs natively" >&2
        crypto=("${native[@]}")
    fi
fi
"${crypto[@]}" RIND_TEST_ARM_NEON=1 RIND_TEST_ARM_CRYPTO_EXT=1 cargo test "${packages[@]}" --locked --release --target "$target"
QEMU_CPU=cortex-a15 RIND_TEST_ARM_NEON=1 RIND_TEST_ARM_CRYPTO_EXT=0 cargo test "${packages[@]}" --locked --release --target "$target"
"${denied[@]}" RIND_CPU_DISABLE_neon=1 RIND_TEST_ARM_NEON=0 RIND_TEST_ARM_CRYPTO_EXT=0 cargo test "${packages[@]}" --locked --release --target "$target"
