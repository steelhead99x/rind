#!/usr/bin/env bash
# Build the prebuilt libraries a release of rind-dart's Dart package pins,
# from the package sh/dart-package.sh staged, as its build hook builds from
# source but for the oldest systems each target supports: Android API 21,
# glibc 2.17 through cargo-zigbuild (as pyrind's manylinux2014 wheels), and
# Rust's default Apple deployment targets. Each lands in OUT_DIR as
# rind_dart-<target>.<extension>, the name sh/dart-prebuilt.sh reads.
#
# Usage: sh/dart-library.sh PACKAGE_DIR OUT_DIR TARGET...
set -euo pipefail

usage="usage: sh/dart-library.sh PACKAGE_DIR OUT_DIR TARGET..."
package=${1:?$usage}
out=${2:?$usage}
shift 2
[[ $# -gt 0 ]] || { echo "$usage" >&2; exit 2; }
mkdir -p "$out"

for target in "$@"; do
    cargo=(cargo)
    triple=$target
    link=()
    case "$target" in
        *-linux-android*)
            ndk=${ANDROID_NDK_HOME:?ANDROID_NDK_HOME must name the Android NDK}
            host=$(uname -s | tr '[:upper:]' '[:lower:]')-x86_64
            link=(--
                "-Clinker=$ndk/toolchains/llvm/prebuilt/$host/bin/clang"
                "-Clink-arg=--target=${target/armv7-/armv7a-}21"
                "-Clink-arg=-Wl,-z,max-page-size=16384")
            ;;
        *-linux-gnu*)
            cargo=(cargo-zigbuild)
            triple=$target.2.17
            ;;
    esac
    case "$target" in
        *-apple-*) file=librind_dart.dylib ext=dylib ;;
        *-windows-*) file=rind_dart.dll ext=dll ;;
        *) file=librind_dart.so ext=so ;;
    esac

    "${cargo[@]}" rustc --release --locked --lib \
        --manifest-path "$package/Cargo.toml" \
        --target "$triple" --target-dir "$package/target" ${link[@]+"${link[@]}"}
    cp "$package/target/$target/release/$file" "$out/rind_dart-$target.$ext"
done
