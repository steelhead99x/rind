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
packages=(-p rind -p rind-rustls -p rind-jsonwebtoken -p rind-object-store -p rind-rcgen -p rind-rand-core -p rind-ring -p rind-digest -p rind-aead -p rind-signature -p rind-kem -p rind-aws-lc-rs -p rind-dimpl -p rind-openmls -p rind-str0m)

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

# shellcheck source=sh/armv7-tiers.sh
source sh/armv7-tiers.sh
# qemu's hang bound (.config/nextest.toml). The doc tests, which only show the
# API, run on the native targets.
export NEXTEST_PROFILE=emulated
# RIND_TEST_ARM_* fails a run on the wrong path.
"${crypto[@]}" RIND_TEST_ARM_NEON=1 RIND_TEST_ARM_CRYPTO_EXT=1 cargo nextest run "${packages[@]}" --locked --release --target "$target"
"${cortex_a15[@]}" RIND_TEST_ARM_NEON=1 RIND_TEST_ARM_CRYPTO_EXT=0 cargo nextest run "${packages[@]}" --locked --release --target "$target"
"${no_neon[@]}" RIND_CPU_DISABLE_neon=1 RIND_TEST_ARM_NEON=0 RIND_TEST_ARM_CRYPTO_EXT=0 cargo nextest run "${packages[@]}" --locked --release --target "$target"
