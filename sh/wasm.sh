#!/usr/bin/env bash
# Run rind's tests on wasm32-wasip2 under wasmtime, as `just wasm` runs it in
# the dev shell's `wasm` shell. wasm compiles the portable backend, so this
# executes the code only wasm compiles, such as MD5's optimizer barrier.
# aws-lc does not build for wasm, so the live differential tests are left out;
# `just portable` runs the same Rust against it on x86_64. Ed25519's CCTV
# vectors still run, against `rind/tests/cctv/ed25519-verdicts.txt`. The other
# vectors run too.
set -euo pipefail

cd "$(dirname "${BASH_SOURCE[0]}")/.."

unfetched=$(git submodule status -- thirdparty/cavp thirdparty/cctv thirdparty/wycheproof | sed -n 's/^-[0-9a-f]* //p')
if [[ -n "$unfetched" ]]; then
    echo "error: test vectors not checked out; run: git submodule update --init ${unfetched//$'\n'/ }" >&2
    exit 1
fi

# The tests open the vector files by their absolute paths under the
# checkout, so wasmtime preopens it at the same path.
root=$(pwd)
# wasmtime passes the guest no host environment unless asked, so SLOW_TESTS
# is forwarded.
export CARGO_TARGET_WASM32_WASIP2_RUNNER="wasmtime run --dir $root::$root --env SLOW_TESTS"

# Optimised, as the armv7 run is, but keeping the checks a debug build has.
export CARGO_PROFILE_RELEASE_DEBUG_ASSERTIONS=true
export CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS=true
SLOW_TESTS=1 cargo test -p rind --features wipe --locked --release --target wasm32-wasip2
