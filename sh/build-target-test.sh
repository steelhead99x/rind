#!/usr/bin/env bash
# Usage: sh/build-target-test.sh
#
# Runs rind/build.rs, compiled on its own, as Cargo would for 32-bit ARM
# targets, and checks the backend and Poly1305 multiply cfgs it prints. A
# custom target specification is classified by its `llvm-target`, never by
# its file name: the same ARMv5TE specification keeps `rind_mul16_top` under
# any name, and one with no `llvm-target` fails closed to it. Needs `rustc`.
set -euo pipefail
cd "$(dirname "$0")/.."

tmp=$(mktemp -d "${TMPDIR:-/tmp}/build-target-test.XXXXXX")
trap 'rm -rf "$tmp"' EXIT
rustc --edition 2024 --crate-name build_script_build -A warnings -o "$tmp/build" rind/build.rs
mkdir "$tmp/specs" "$tmp/pkg"

spec() { # file-stem llvm-target-or-empty
    local llvm=""
    [[ -z $2 ]] || llvm="\"llvm-target\": \"$2\","
    cat >"$tmp/specs/$1.json" <<EOF
{
    "arch": "arm",
    $llvm
    "data-layout": "e-m:e-p:32:32-Fi8-i64:64-v128:64:128-a:0:32-n32-S64",
    "target-pointer-width": 32,
    "os": "none"
}
EOF
}

status=0
# check NAME TARGET OS WANT... : each WANT is a cfg line that must be printed,
# or `!cfg` for one that must not.
check() {
    local name=$1 target=$2 os=$3 out
    shift 3
    out=$(env -u CARGO_ENCODED_RUSTFLAGS -u CARGO_CFG_RIND_MUL16 -u CARGO_CFG_RIND_MUL16_TOP \
        -u CARGO_CFG_RIND_MUL16_SOFT -u CARGO_CFG_RIND_PORTABLE -u CARGO_CFG_RIND_LIMB \
        TARGET="$target" RUST_TARGET_PATH="$tmp/specs" CARGO_MANIFEST_DIR="$tmp/pkg" \
        CARGO_CFG_TARGET_OS="$os" CARGO_CFG_TARGET_ENV="" CARGO_CFG_TARGET_ARCH=arm \
        CARGO_CFG_TARGET_ENDIAN=little CARGO_CFG_TARGET_POINTER_WIDTH=32 \
        CARGO_CFG_TARGET_FEATURE="" "$tmp/build")
    local want
    for want in "$@"; do
        if [[ $want == '!'* ]]; then
            if grep -qxF "cargo::rustc-cfg=${want#!}" <<<"$out"; then
                echo "build-target-test: $name printed ${want#!}" >&2
                status=1
            fi
        elif ! grep -qxF "cargo::rustc-cfg=$want" <<<"$out"; then
            echo "build-target-test: $name did not print $want" >&2
            status=1
        fi
    done
}

# Built-in triples.
check armv5te armv5te-unknown-linux-gnueabi linux rind_mul16 rind_mul16_top 'rind_backend="portable"'
check thumbv7m thumbv7m-none-eabi none rind_mul16 '!rind_mul16_top' 'rind_backend="portable"'
check armv7 armv7-unknown-linux-gnueabihf linux '!rind_mul16' 'rind_backend="arm"'

# One ARMv5TE specification under a plain name, a later-looking one, and an
# ARMv6 triple's: the file name changes nothing.
for stem in board armv7-board thumbv7em-board arm-unknown-linux-gnueabi; do
    spec "$stem" armv5te-none-eabi
    check "ARMv5TE spec $stem.json" "$stem" none rind_mul16 rind_mul16_top 'rind_backend="portable"'
done
# A Cortex-M3 specification named like ARMv7-A is still M-profile.
spec armv7a-mcu thumbv7m-none-eabi
check "thumbv7m spec armv7a-mcu.json" armv7a-mcu none rind_mul16 '!rind_mul16_top' 'rind_backend="portable"'
# No `llvm-target`: the core is unknown, so the top bit stays set.
spec armv7-nollvm ""
check "spec without llvm-target" armv7-nollvm none rind_mul16 rind_mul16_top 'rind_backend="portable"'

exit "$status"
