#!/usr/bin/env bash
# Build the rind-openssl library a release ships for TARGET into OUT_DIR as
# rind_openssl-<target>.<extension>, for the oldest systems the target
# supports: glibc 2.17 through cargo-zigbuild, as sh/dart-library.sh builds
# rind-dart's, and Rust's default Apple deployment target. Fails if a Linux
# build needs a newer glibc symbol than that floor.
#
# Usage: sh/openssl-library.sh OUT_DIR TARGET
set -euo pipefail

usage="usage: sh/openssl-library.sh OUT_DIR TARGET"
out=${1:?$usage}
target=${2:?$usage}
[[ $# -eq 2 ]] || { echo "$usage" >&2; exit 2; }

cd "$(git rev-parse --show-toplevel)"
mkdir -p "$out"

case "$target" in
    *-linux-gnu*) cargo=(cargo-zigbuild) triple=$target.2.17 file=librind_openssl.so ext=so ;;
    *-apple-darwin) cargo=(cargo) triple=$target file=librind_openssl.dylib ext=dylib ;;
    *)
        echo "error: rind-openssl releases no library for $target" >&2
        exit 2
        ;;
esac

"${cargo[@]}" build --release --locked -p rind-openssl --lib --target "$triple"
library="$out/rind_openssl-$target.$ext"
cp "target/$target/release/$file" "$library"

if [[ "$ext" == so ]]; then
    newest=$(objdump -T "$library" | grep -oE 'GLIBC_[0-9.]+' | sed 's/GLIBC_//' | sort -uV | tail -n 1)
    if [[ "$(printf '%s\n' "$newest" 2.17 | sort -V | tail -n 1)" != 2.17 ]]; then
        echo "error: $library needs glibc $newest, past the 2.17 floor" >&2
        exit 1
    fi
fi
echo "$library"
