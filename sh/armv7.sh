#!/usr/bin/env bash
# Build, lint, and test the armv7 targets, as `just armv7` runs it inside the
# flake's `armv7` dev shell. The gnueabihf tests run under qemu-user three
# times, to cover each of rind's armv7 tiers.
set -euo pipefail

if [[ -z "${CARGO_TARGET_ARMV7_UNKNOWN_LINUX_GNUEABIHF_RUNNER:-}" ]]; then
    echo "error: run through 'just armv7', which enters the flake's armv7 dev shell" >&2
    exit 1
fi

cd "$(dirname "${BASH_SOURCE[0]}")/.."

# Fail before the long cross build rather than partway through the tests.
unfetched=$(git submodule status -- thirdparty/cavp thirdparty/cctv thirdparty/wycheproof | sed -n 's/^-[0-9a-f]* //p')
if [[ -n "$unfetched" ]]; then
    echo "error: test vectors not checked out; run: git submodule update --init ${unfetched//$'\n'/ }" >&2
    exit 1
fi

# The bench and fuzz crates need C libraries built for the target.
packages=(-p rind -p rind-rustls -p rind-jsonwebtoken -p rind-object-store -p rind-rcgen -p rind-ring -p rind-aws-lc-rs -p rind-dimpl -p rind-str0m)

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

# `max` has the ARMv8 crypto extension, and so NEON; the Cortex-A15 is ARMv7
# with NEON but without the extension, and denying its NEON leaves only the
# scalar paths. RIND_TEST_ARM_* fails the run that lands on the wrong path.
QEMU_CPU=max RIND_TEST_ARM_NEON=1 RIND_TEST_ARM_CRYPTO_EXT=1 cargo test "${packages[@]}" --locked --release --target "$target"
QEMU_CPU=cortex-a15 RIND_TEST_ARM_NEON=1 RIND_TEST_ARM_CRYPTO_EXT=0 cargo test "${packages[@]}" --locked --release --target "$target"
QEMU_CPU=cortex-a15 RIND_CPU_DISABLE_neon=1 RIND_TEST_ARM_NEON=0 RIND_TEST_ARM_CRYPTO_EXT=0 cargo test "${packages[@]}" --locked --release --target "$target"
QEMU_CPU=max RIND_TEST_ARM_NEON=1 RIND_TEST_ARM_CRYPTO_EXT=1 cargo test -p rind --features wipe --test zeroing --test heap_scratch --locked --release --target "$target"
QEMU_CPU=cortex-a15 RIND_TEST_ARM_NEON=1 RIND_TEST_ARM_CRYPTO_EXT=0 cargo test -p rind --features wipe --test zeroing --test heap_scratch --locked --release --target "$target"
QEMU_CPU=cortex-a15 RIND_CPU_DISABLE_neon=1 RIND_TEST_ARM_NEON=0 RIND_TEST_ARM_CRYPTO_EXT=0 cargo test -p rind --features wipe --test zeroing --test heap_scratch --locked --release --target "$target"
