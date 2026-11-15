#!/usr/bin/env bash
# Run rind's tests on wasm32-wasip2 under wasmtime, as `just wasm` runs it in
# the dev shell's `wasm` shell. wasm compiles the portable backend, so this
# executes the code only wasm compiles, such as MD5's optimizer barrier.
# aws-lc does not build for wasm, so the live differential tests are left out;
# `just portable` runs the same Rust against it on x86_64. Ed25519's CCTV
# vectors still run, against `rind/tests/cctv/ed25519-verdicts.txt`. The other
# vectors run too.
#
# `sh/dispatch.sh` sources this file for `wasm_runner` and does not run the
# suite below. Sourcing stops after the function.

# Point Cargo's wasm32-wasip2 runner at wasmtime and preopen the checkout at
# the absolute path the tests use to open fixtures. wasmtime passes the guest
# no host environment unless asked, so SLOW_TESTS is forwarded. When the host
# has not set it, the guest does not see it either.
wasm_runner() {
    local root
    root=$(pwd)
    export CARGO_TARGET_WASM32_WASIP2_RUNNER="wasmtime run --dir ${root}::${root} --env SLOW_TESTS"
}

if [[ ${BASH_SOURCE[0]} == "$0" ]]; then
    set -euo pipefail

    cd "$(dirname "${BASH_SOURCE[0]}")/.."

    # Optimised, as the armv7 run is, but keeping the checks a debug build has.
    export CARGO_PROFILE_RELEASE_DEBUG_ASSERTIONS=true
    export CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS=true
    export SLOW_TESTS=1
    wasm_runner
    cargo test -p rind --features wipe --locked --release --target wasm32-wasip2
fi
