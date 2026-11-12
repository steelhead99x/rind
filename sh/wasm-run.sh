#!/usr/bin/env bash
# wasmtime runner for `cargo test --target wasm32-wasip2`.
#
# Cargo appends the test component and its arguments. The repository is
# preopened at the host path the tests bake in with `CARGO_MANIFEST_DIR`, so
# `../thirdparty` resolves inside that one directory. The script locates that
# path itself: Cargo splits a runner string on whitespace, so `sh/wasm.sh`
# passes this file as one config-array entry and nothing else.
#
# The guest does not inherit the host environment. Forward the variables the
# slow sets and proptest read. `sh/wasm.sh` prints the proptest seed: a wasm
# panic aborts before proptest can print the seed it drew or shrink the case.
set -euo pipefail

root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
component=${1:?test component}
shift

args=(run --dir "${root}::${root}")
forward() {
    local name=$1
    if [[ -v $name ]]; then
        args+=(--env "${name}=${!name}")
    fi
}
forward SLOW_TESTS
forward PROPTEST_CASES
forward PROPTEST_RNG_SEED
echo "wasm-run: SLOW_TESTS=${SLOW_TESTS-<unset>} PROPTEST_CASES=${PROPTEST_CASES-<unset>} PROPTEST_RNG_SEED=${PROPTEST_RNG_SEED-<unset>}" >&2

# No "--" before the test arguments. libtest treats everything after "--" as
# a test-name filter, so a later flag such as --exact would match nothing and
# the run would pass having run no test.
args+=("$component")
if [[ $# -gt 0 ]]; then
    args+=("$@")
fi

log=$(mktemp)
trap 'rm -f "$log"' EXIT
set +e
wasmtime "${args[@]}" | tee "$log"
status=${PIPESTATUS[0]}
set -e
# A harness with no tests exits 0. A name filter that matches nothing reports
# those tests as filtered out, so this fires only for an empty harness.
# `sh/wasm.sh` also fails the whole cargo invocation when no harness ran a test.
if [[ "$status" -eq 0 ]] && grep -Eq '^test result: ok\. 0 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out;' "$log"; then
    echo "error: ${component} ran no tests" >&2
    exit 1
fi
exit "$status"
