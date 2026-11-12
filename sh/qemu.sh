#!/usr/bin/env bash
# Build, lint, and test a target with no rind assembly, under qemu-user
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

# Fail before the long cross build rather than partway through the tests.
unfetched=$(git submodule status -- thirdparty/cavp thirdparty/cctv thirdparty/wycheproof | sed -n 's/^-[0-9a-f]* //p')
if [[ -n "$unfetched" ]]; then
    echo "error: test vectors not checked out; run: git submodule update --init ${unfetched//$'\n'/ }" >&2
    exit 1
fi

# The bench and fuzz crates need C libraries built for the target.
packages=(-p rind -p rind-rustls -p rind-jsonwebtoken -p rind-object-store -p rind-rcgen -p rind-ring -p rind-aws-lc-rs -p rind-dimpl -p rind-str0m)

export CARGO_PROFILE_RELEASE_DEBUG_ASSERTIONS=true
export CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS=true

# Linted in the profile the tests build, since nixpkgs' cross gcc warns about
# _FORTIFY_SOURCE at -O0, which fails aws-lc's compiler probes and so its
# big-endian build.
cargo clippy "${packages[@]}" --locked --release --target "$target" --all-targets -- --deny warnings
cargo test "${packages[@]}" --locked --release --target "$target"
cargo test -p rind --features wipe --test zeroing --test heap_scratch --locked --release --target "$target"
