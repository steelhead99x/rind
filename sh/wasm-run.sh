#!/usr/bin/env bash
# wasmtime runner for `cargo test --target wasm32-wasip2`.
#
# Cargo appends the test component and its arguments. The repository is
# preopened at the host path the tests bake in with `CARGO_MANIFEST_DIR`, so
# `../thirdparty` resolves inside that one directory.
set -euo pipefail

root=${1:?repository root}
shift
component=${1:?test component}
shift
exec wasmtime run --dir "${root}::${root}" "$component" -- "$@"
