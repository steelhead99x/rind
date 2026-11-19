#!/usr/bin/env bash
# Build, lint, and test a target other than armv7, under qemu-user
# unless the host runs it natively, as `just qemu <shell>` runs it inside that
# flake dev shell, which names the target. Optimised for qemu, but keeping the
# checks a debug build has.
set -euo pipefail

target=${RIND_QEMU_TARGET:-}
if [[ -z "$target" ]]; then
    echo "error: run through 'just qemu <shell>', which enters a flake dev shell naming the target" >&2
    exit 1
fi

cd "$(dirname "${BASH_SOURCE[0]}")/.."

# The bench and fuzz crates need C libraries built for the target.
packages=(-p rind -p rind-rustls -p rind-jsonwebtoken -p rind-object-store -p rind-rcgen -p rind-ring -p rind-aws-lc-rs -p rind-dimpl -p rind-openmls -p rind-str0m)

export CARGO_PROFILE_RELEASE_DEBUG_ASSERTIONS=true
export CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS=true

# Linted in the profile the tests build, since nixpkgs' cross gcc warns about
# _FORTIFY_SOURCE at -O0, which fails aws-lc's compiler probes and so its
# big-endian build.
cargo clippy "${packages[@]}" --locked --release --target "$target" --all-targets -- --deny warnings
cargo test "${packages[@]}" --locked --release --target "$target"
