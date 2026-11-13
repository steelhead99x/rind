#!/usr/bin/env bash
# Lint and test the portable backend, as `just portable` runs it in the dev
# shell. `--cfg rind_portable` forces it on this x86_64 Linux host, so it runs
# without emulation, and dalek's serial backend is the one the architectures
# that need the portable backend run, rather than the AVX2 one dalek picks
# here.
set -euo pipefail

if [[ "$(uname -sm)" != "Linux x86_64" ]]; then
    echo "error: 'just portable' forces the portable backend on x86_64 Linux" >&2
    exit 1
fi

cd "$(dirname "${BASH_SOURCE[0]}")/.."

# Fail before the build rather than partway through the tests.
unfetched=$(git submodule status -- thirdparty/cavp thirdparty/wycheproof | sed -n 's/^-[0-9a-f]* //p')
if [[ -n "$unfetched" ]]; then
    echo "error: test vectors not checked out; run: git submodule update --init ${unfetched//$'\n'/ }" >&2
    exit 1
fi

# The bench and fuzz crates compare against other libraries, not backends.
packages=(-p rind -p rind-rustls -p rind-jsonwebtoken -p rind-object-store -p rind-rcgen -p rind-ring -p rind-dimpl -p rind-openmls)

# The explicit target keeps these builds apart from the host's, whose flags
# differ.
target=x86_64-unknown-linux-gnu
export CARGO_TARGET_X86_64_UNKNOWN_LINUX_GNU_RUSTFLAGS='--cfg rind_portable --cfg curve25519_dalek_backend="serial"'
cargo clippy "${packages[@]}" --locked --target "$target" --all-targets -- --deny warnings

# Optimised, as the armv7 run is, but keeping the checks a debug build has.
export CARGO_PROFILE_RELEASE_DEBUG_ASSERTIONS=true
export CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS=true
SLOW_TESTS=1 cargo test "${packages[@]}" --locked --release --target "$target"
SLOW_TESTS=1 cargo test -p rind --features wipe --test zeroing --test heap_scratch --locked --release --target "$target"
# wasm32's portable build runs on 32-bit limbs, and `just wasm` generates
# only RSA-2048 keys, so RSA-3072 and RSA-4096 key generation on those limbs
# is wipe-checked here, natively.
CARGO_TARGET_X86_64_UNKNOWN_LINUX_GNU_RUSTFLAGS="$CARGO_TARGET_X86_64_UNKNOWN_LINUX_GNU_RUSTFLAGS --cfg rind_limb=\"32\"" \
    SLOW_TESTS=1 cargo test -p rind --features wipe --test heap_scratch --locked --release --target "$target" -- rsa_generate
