#!/usr/bin/env bash
# Lint and test rind on wasm32-wasip2 under wasmtime, as `just wasm` runs it
# inside the flake's `wasm` dev shell. aws-lc-rs does not build for wasm, so
# the differential tests stay out; the vectors run. wasm32-unknown-unknown
# stays a compile check: its tests need a JavaScript host.
set -euo pipefail

if ! command -v wasmtime >/dev/null; then
    echo "error: run through 'just wasm', which enters the flake's wasm dev shell" >&2
    exit 1
fi

cd "$(dirname "${BASH_SOURCE[0]}")/.."
root=$(pwd)

# Fail before the build rather than partway through the tests.
unfetched=$(git submodule status -- thirdparty/cavp thirdparty/cctv thirdparty/wycheproof | sed -n 's/^-[0-9a-f]* //p')
if [[ -n "$unfetched" ]]; then
    echo "error: test vectors not checked out; run: git submodule update --init ${unfetched//$'\n'/ }" >&2
    exit 1
fi

target=wasm32-wasip2
export CARGO_TARGET_WASM32_WASIP2_RUNNER="${root}/sh/wasm-run.sh ${root}"

# Optimised, as the qemu runs are, but keeping the checks a debug build has.
export CARGO_PROFILE_RELEASE_DEBUG_ASSERTIONS=true
export CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS=true

cargo clippy -p rind --locked --target "$target" --all-targets -- --deny warnings
cargo test -p rind --locked --release --target "$target"
cargo test -p rind --features wipe --test zeroing --test heap_scratch --locked --release --target "$target"

# wasip2 randomness is WASI's. The browser target's ring feature must select
# getrandom's JavaScript backend, and must not be required for wasip2.
cargo clippy -p rind-ring --lib --locked --target "$target" -- --deny warnings
cargo clippy -p rind-ring --lib --locked --target wasm32-unknown-unknown \
    --features wasm32_unknown_unknown_js -- --deny warnings
