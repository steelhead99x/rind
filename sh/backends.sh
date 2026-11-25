#!/usr/bin/env bash
# The rind backends a diff can break: x86_64, aarch64, arm (armv7), and
# portable. `just check`'s cross, msrv, and vartime modules check only the
# reached backends' builds.
#
# Usage: sh/backends.sh CHANGED_FILE
#
# CHANGED_FILE lists the changed paths, one per line, as sh/changed.sh prints
# them; `-` reads them from stdin. Prints the reached backends one per line,
# sorted, `all` when the diff can reach every one, or `none`.
set -euo pipefail

if [[ $# -ne 1 ]]; then
    echo "usage: sh/backends.sh CHANGED_FILE" >&2
    exit 2
fi
changed=$1
[[ "$changed" != - ]] || changed=/dev/stdin

# Outside rind's crate, these reach every backend: the dependencies, the
# toolchain, the test vectors, the recipes, scripts, workflows, and local
# actions that run ctgrind, and the adapters, whose tests ctgrind runs too,
# along with any Rust crate nested in one, such as the FIPS module in
# rind-fips/module/ (Dart's lib/src/ is not one), and rind-openssl's
# openssl.cnf, which its tests embed.
shared='^(Cargo\.(toml|lock)$|flake\.(nix|lock)$|rust-toolchain(\.toml)?$|\.cargo/|justfile$|thirdparty/|sh/(backends|changed)\.sh$|admin/ctgrind|\.github/(workflows/ctgrind\.yml$|actions/)|rind-[a-z0-9-]+/((src/|tests/|build\.rs$|Cargo\.toml$)|([^/]+/)+(src/.*\.rs$|build\.rs$|Cargo\.toml$))|rind-openssl/openssl\.cnf$)'

# It reads every line, even once it knows the answer, so a writer piping a
# long diff in never meets a closed pipe.
declare -A backends=()
all=''
while IFS= read -r path; do
    [[ -n "$path" && -z "$all" ]] || continue
    if [[ "$path" =~ $shared ]]; then
        all=1
        continue
    fi
    # The rest of rind's crate, such as its manifest, build script, tests, and
    # proptest regressions, reaches every backend, all but its docs and
    # license. Anything else outside rind/src/, such as docs, quests, or
    # rind-bench, builds into no backend.
    if [[ "$path" != rind/src/* ]]; then
        [[ "$path" != rind/* || "$path" =~ ^rind/([^/]+\.md|LICENSE)$ ]] || all=1
        continue
    fi

    # Each low/ directory compiles into its own backend, but armv7 builds on
    # the portable backend's, and aarch64 shares armv7's qemu constant-time
    # hooks. mid/portable/ swaps in for both. Every other file is shared.
    case "${path#rind/src/}" in
        low/x86_64/*) reach=(x86_64) ;;
        low/aarch64/*) reach=(aarch64) ;;
        low/arm/ct_qemu.rs) reach=(arm aarch64) ;;
        low/arm/*) reach=(arm) ;;
        low/portable/* | mid/portable/*) reach=(arm portable) ;;
        *)
            all=1
            continue
            ;;
    esac
    for name in "${reach[@]}"; do backends[$name]=1; done
done <"$changed"

if [[ -n "$all" ]]; then
    echo all
elif ((${#backends[@]} == 0)); then
    echo none
else
    printf '%s\n' "${!backends[@]}" | sort
fi
