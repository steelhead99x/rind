#!/usr/bin/env bash
# Lint and test rind on wasm32-wasip2 under wasmtime, as `just wasm` runs it
# inside the flake's `wasm` dev shell. aws-lc-rs does not build for wasm, so
# the differential tests stay out. The vectors run, including every set
# `SLOW_TESTS` gates. Ed25519's CCTV verdicts are compared with a file
# recorded from aws-lc. wasm32-unknown-unknown stays a compile check: its
# tests need a JavaScript host.
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

# Cargo splits CARGO_TARGET_*_RUNNER on whitespace, which breaks a repository
# path that contains a space and cannot pass this script one argument. A
# config array is one argv, and the script finds the repository itself.
export CARGO_TERM_COLOR=never
runner_toml=${root//\\/\\\\}
runner_toml=${runner_toml//\"/\\\"}
cargo=(cargo --config "target.${target}.runner=[\"${runner_toml}/sh/wasm-run.sh\"]")

# Optimised, as the qemu runs are, but keeping the checks a debug build has.
export CARGO_PROFILE_RELEASE_DEBUG_ASSERTIONS=true
export CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS=true

# The guest does not see the host environment; sh/wasm-run.sh forwards these.
# `portable.sh` runs the same slow sets.
export SLOW_TESTS=1
# A wasm panic aborts before proptest prints the seed it drew, and proptest
# does not read PROPTEST_RNG_SEED on wasm32. The wasm proptest blocks apply
# this value. Keep the caller's seed when one is set, and always print it so
# a failure replays. Shrinking does not run: the panic aborts first.
: "${PROPTEST_RNG_SEED:=1}"
export PROPTEST_RNG_SEED
echo "PROPTEST_RNG_SEED=${PROPTEST_RNG_SEED}"

"${cargo[@]}" clippy -p rind --locked --target "$target" --all-targets -- --deny warnings

# `crosschecks.rs` needs aws-lc. `zeroing.rs` and `heap_scratch.rs` are empty
# without `wipe` and run in the command below. The runner fails an empty
# harness, and this fails the invocation if a filter matched nothing.
tests=()
for path in rind/tests/*.rs; do
    name=$(basename "$path" .rs)
    case "$name" in
        crosschecks | zeroing | heap_scratch) continue ;;
    esac
    tests+=(--test "$name")
done

run_tests() {
    local log status
    log=$(mktemp)
    set +e
    "${cargo[@]}" "$@" 2>&1 | tee "$log"
    status=${PIPESTATUS[0]}
    set -e
    if [[ "$status" -ne 0 ]]; then
        rm -f "$log"
        exit "$status"
    fi
    if ! grep -Eq '^running [1-9][0-9]* tests$' "$log"; then
        echo "error: cargo $* ran no tests" >&2
        rm -f "$log"
        exit 1
    fi
    rm -f "$log"
}

run_tests test -p rind --locked --release --target "$target" --lib "${tests[@]}" -- --nocapture
run_tests test -p rind --locked --release --target "$target" --doc
run_tests test -p rind --features wipe --test zeroing --test heap_scratch --locked --release --target "$target" -- --nocapture

# wasip2 randomness is WASI's. The browser target's ring feature must select
# getrandom's JavaScript backend, and must not be required for wasip2.
"${cargo[@]}" clippy -p rind-ring --lib --locked --target "$target" -- --deny warnings
"${cargo[@]}" clippy -p rind-ring --lib --locked --target wasm32-unknown-unknown \
    --features wasm32_unknown_unknown_js -- --deny warnings
