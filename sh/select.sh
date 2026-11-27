#!/usr/bin/env bash
# Print the Cargo package arguments for the crates a diff touches, plus every
# workspace crate depending on them, one argument per line.
#
# Usage: sh/select.sh CHANGED_FILE [ALL] [--lib|--no-dependents-on-low]
# A change outside any crate's directory (the root manifest, the lockfile,
# thirdparty/ test vectors, the flake's toolchain) can reach every crate, so it
# selects --workspace, as does a non-empty ALL. --lib keeps only the crates with
# a library, which `cargo test --doc` requires. --no-dependents-on-low, for
# `just check`, leaves out rind's dependents when the diff changes rind only
# under rind/src/low/, outside the CPU dispatch every primitive shares: that
# code is private, so rind's own tests cover it, and `just ci` still runs the
# dependents.
set -euo pipefail

usage="usage: sh/select.sh CHANGED_FILE [ALL] [--lib|--no-dependents-on-low]"
changed=${1:?$usage}
all=${2:-}
mode=${3:-}
if [[ $# -gt 3 || (-n "$mode" && "$mode" != --lib && "$mode" != --no-dependents-on-low) ]]; then
    echo "$usage" >&2
    exit 2
fi

if [[ -n "$all" ]]; then
    echo --workspace
    exit
fi

root=$(git rev-parse --show-toplevel)
metadata=$(cargo metadata --format-version 1 --no-deps --locked)

# Each member's directory, relative to the root, and its name.
declare -A dirs=()
while IFS=$'\t' read -r dir name; do
    dirs[$dir]=$name
done < <(jq -r --arg root "$root/" '.packages[] | [(.manifest_path | ltrimstr($root) | rtrimstr("/Cargo.toml")), .name] | @tsv' <<<"$metadata")

declare -A selected=()
while IFS= read -r path; do
    # The innermost crate directory holding the path, so a nested crate such
    # as rind-fips/module is selected rather than its parent.
    dir=${path%/*}
    while [[ "$dir" == */* && -z "${dirs[$dir]:-}" ]]; do
        dir=${dir%/*}
    done
    if [[ "$path" == */* && -n "${dirs[$dir]:-}" ]]; then
        selected[${dirs[$dir]}]=1
    elif grep -qE '^(thirdparty/|Cargo\.(toml|lock)$|\.rustfmt(\.unstable)?\.toml$|flake\.(nix|lock)$)' <<<"$path"; then
        echo --workspace
        exit
    fi
done <"$changed"

# Add workspace dependents until nothing new appears. rind-fips's build
# script builds rind-fips-module with a cargo of its own, an edge the
# metadata does not show.
edges=$(jq -r '.packages[] | .name as $n | .dependencies[] | select(.path != null) | [.name, $n] | @tsv' <<<"$metadata")
edges+=$'\nrind-fips-module\trind-fips'
if [[ "$mode" == --no-dependents-on-low ]] && grep -q '^rind/' "$changed" &&
    ! grep '^rind/' "$changed" | grep -qvE '^rind/src/low/' &&
    ! grep -qE '^rind/src/low/((mod|entry|cpu|mcdt|mcdt_none|macros|abi|inline_assembly_safety)\.rs|abi/.+|[^/]+/(mod|cpu)\.rs)$' "$changed"; then
    edges=$(grep -v $'^rind\t' <<<"$edges")
fi
grew=1
while [[ -n "$grew" ]]; do
    grew=
    while IFS=$'\t' read -r dep dependent; do
        if [[ -n "${selected[$dep]:-}" && -z "${selected[$dependent]:-}" ]]; then
            selected[$dependent]=1
            grew=1
        fi
    done <<<"$edges"
done

libs=$(jq -r '.packages[] | select(any(.targets[]; .kind | index("lib"))) | .name' <<<"$metadata")
for name in "${!selected[@]}"; do
    if [[ "$mode" != --lib ]] || grep -qxF "$name" <<<"$libs"; then
        printf -- '-p\n%s\n' "$name"
    fi
done
