#!/usr/bin/env bash
# Run rind's tests, and rind-rustls's and rind-ring's, on wasm32-wasip2 under
# wasmtime, then the adapters' again on wasm32-unknown-unknown, the browser's
# target, under wasm-bindgen's test runner in Node, as `just wasm` runs it in
# the dev shell's `wasm` shell. wasm compiles the portable backend, so this
# executes the code only wasm compiles, such as MD5's optimizer barrier. aws-lc
# does not build for wasm, so the differential tests are left out; `just
# portable` runs the same Rust against it on x86_64. The vectors run, and the
# adapters' handshakes run rind against itself.
set -euo pipefail

cd "$(dirname "${BASH_SOURCE[0]}")/.."

# The tests open the vector files by their absolute paths under the
# checkout, so wasmtime preopens it at the same path.
root=$(pwd)
# wasmtime passes the guest no host environment unless asked, so SLOW_TESTS
# is forwarded.
export CARGO_TARGET_WASM32_WASIP2_RUNNER="wasmtime run --dir $root::$root --env SLOW_TESTS"

# Optimised, as the armv7 run is, but keeping the checks a debug build has.
export CARGO_PROFILE_RELEASE_DEBUG_ASSERTIONS=true
export CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS=true
SLOW_TESTS=1 cargo test -p rind --locked --release --target wasm32-wasip2
# Without the examples, whose tokio needs the threads and sockets wasm lacks.
cargo test -p rind-rustls -p rind-ring --lib --tests --locked --release --target wasm32-wasip2

# The browser's target runs the same code but for what it takes from
# JavaScript: rind's random source and rustls's clock. rind's own tests read
# their vectors from files, which it has no way to open, so only the adapters'
# run there, with their vectors and keys compiled in.
export CARGO_TARGET_WASM32_UNKNOWN_UNKNOWN_RUNNER=wasm-bindgen-test-runner
cargo test -p rind-ring --test ring --features wasm32_unknown_unknown_js --locked --release --target wasm32-unknown-unknown
cargo test -p rind-rustls --lib --tests --locked --release --target wasm32-unknown-unknown
